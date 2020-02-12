#define NUM_CPU 2
#define MEM_SIZE 4

// Has to be power of 2
#define CACHE_SIZE 1 

//Cache line states
#define INVALID 0
#define SHARED 1
#define EXCLUSIVE 2
#define MODIFIED 3

//Messages
#define NONE  0
#define READ  1
#define READX 2
#define UPGRD 3
#define FLUSH 4

#define ADDRESS_TO_CACHE_LINE(a) (a & (CACHE_SIZE - 1))
#define GET_STATE(c, id, adr) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag & 3)
#define SET_STATE(c, id, adr, st) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag = ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag) & (~3)) | ((st) & 3))

#define GET_TAG(c, id, adr) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag >> 2)
#define SET_TAG(c, id, adr) ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag) = ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag) & 3) | (((adr) & 63) << 2))

#define GET_VALUE(c, id, adr) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].data)
#define SET_VALUE(c, id, adr, val) ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].data) = (val))

typedef cache_line {
    // bits 0 to 1 are used for cache line state
    // bits 2 to 7 are used for adress tag 
    byte tag;
    byte data;
};

typedef cache {
    cache_line lines[CACHE_SIZE];
}

chan bus_c = [0] of {byte, byte, byte, byte};
chan cpu_in[NUM_CPU] = [0] of {byte, byte};
chan cpu_out[NUM_CPU] = [0] of {bool, byte};

byte mem[MEM_SIZE];
cache caches[NUM_CPU];


proctype bus() {
    byte i;
    byte cpu_id;
    byte msg_type;
    byte address;
    byte data;
    byte rep_msg_type;
    byte rep_address;
    byte rep_data;
    do
        ::bus_c ? cpu_id, msg_type, address, data  -> 
            assert(msg_type != NONE);

            for (i : 0 .. NUM_CPU - 1) {
                if 
                :: i != cpu_id 
                    cpu_in[i] ! msg_type, address, data;
                    cpu_out[i] ? rep_msg_type, rep_address, rep_data;
                    
                    assert(rep_msg_type == NONE || rep_msg_type == FLUSH);
                    assert(!(msg_type == FLUSH && rep_msg_type == FLUSH));
                    assert(rep_address == address);

                    if 
                    :: rep_msg_type == NONE -> skip;
                    :: rep_msg_type == FLUSH -> mem[rep_address] = rep_data; 
                    fi
                fi
            }

            if 
            :: msg_type == FLUSH -> mem[address] = data;
            fi
            cpu_in[cpu_id] ! msg_type, address, mem[address]
    od
}

inline update_required_bus_op() {
    //Bus operation needed based on the cache state and tag
    if 
    :: cache_tag != address -> 
        if 
        :: cache_state == MODIFIED -> bus_op = FLUSH;
        :: else -> 
            if 
            :: read -> bus_op = READ;
            :: !read -> bus_op = READX;
            fi
        fi
    :: cache_tag == address ->
        if 
        :: cache_state == INVALID -> 
            if 
            :: read -> bus_op = READ;
            :: !read -> bus_op = READX;
            fi
        :: cache_state == SHARED -> 
            if
            :: read -> bus_op = NONE;
            :: !read -> bus_op = UPGRD;
            fi 
        :: cache_state == EXCLUSIVE -> bus_op = NONE;
        :: cache_state == MODIFIED -> bus_op = NONE;
        fi
    fi
}

inline generate_request() {
    if 
    :: read = true;
    :: read = false;
    fi
    if 
    :: address = 0;
    :: address = 1;
    :: address = 2;
    :: address = 3;
    fi
    cache_state = GET_STATE(caches, id, address);
    cache_tag = GET_TAG(caches, id, address); 

    update_required_bus_op(); 
}

inline modify_cache() {
    SET_STATE(caches, id, address, MODIFIED);
    SET_VALUE(caches, id, address, value);
}

inline read_from_cache() {
    assert(GET_VALUE(caches, id, address) == value);
}

inline update_cache_own_op() {
    if 
    :: bus_op == READ  ->
        SET_STATE(caches, id, address, SHARED);
        SET_TAG(caches, id, address);
        SET_VALUE(caches, id, address, data);
    :: bus_op == READX ->
        SET_STATE(caches, id, address, EXCLUSIVE);
        SET_TAG(caches, id, address);
        SET_VALUE(caches, id, address, data);
    :: bus_op == UPGRD -> SET_STATE(caches, id, address, EXCLUSIVE);
    :: bus_op == FLUSH -> SET_STATE(caches, id, address, SHARED);
    fi
}

inline update_cache_snooped_op() {
    reply_op = NONE;
    reply_adr = snp_address;
    reply_data = 0;

    // If the address is stored in our cache
    if
    :: GET_TAG(caches, id, snp_address) == snp_address && snp_state != INVALID ->
        
        assert(snp_bus_op != FLUSH); // FLUSH should never happen while we have the cache line in valid state
        
        if
        :: snp_state == MODIFIED -> //FLUSH
            reply_op = FLUSH;
            reply_adr = snp_address;
            reply_data = GET_VALUE(caches, id, snp_address);
        fi
        
        if
        :: snp_bus_op == READ -> SET_STATE(caches, id, snp_address, SHARED);
        :: snp_bus_op == READX -> SET_STATE(caches, id, snp_address, INVALID);
        :: snp_bus_op == UPGRD -> SET_STATE(caches, id, snp_address, INVALID);
        fi
    :: else -> skip;
    fi    
}

inline execute_in_cache() {
    assert(bus_op == NONE);
    if
    :: read -> read_from_cache();
    :: !read -> modify_cache();
    fi   
}

proctype cpu(byte id) {
    //Read or write
    bool read;
    byte address;
    byte cache_state; 
    byte cache_tag;  
    byte bus_op;

    generate_request();

    do
        :: skip ->
            if 
            :: bus_op != NONE && (bus_c ! id, bus_op, address, data) -> //DO THE COMMUNICATION
                cpu_in[id] ? bus_op, address, data;
                update_cache_own_op();
                update_required_bus_op();
                execute_in_cache();
            :: else ->
                byte snp_bus_op;
                byte snp_address;
                byte snp_data;
                byte snp_state;
                if 
                :: cpu_in[id] ? snp_bus_op, snp_address, snp_data -> // snoop from the bus, change the request based on the updates
                    byte reply_op;
                    byte reply_adr;
                    byte reply_data;
                    snp_state = GET_STATE(cache, id, address);
                    update_cache_snooped_op();
                    update_required_bus_op();
                    cpu_out[id] ! reply_op, reply_adr, reply_data;
                :: bus_op == NONE ->  // try execute request, do nothing if needs com
                    execute_in_cache();
                    generate_request(); //Generate new request
                :: else -> skip; //Try to acquire the bus and snoop some more 
                fi 
            fi
    od
}

proctype cache_state_check() {
    byte adr;
    byte cpu_id;
    d_step{
        for (adr: 0 .. MEM_SIZE - 1) {
            byte state_cnt[4];
            byte value = mem[adr];
            for (cpu_id: 0 .. NUM_CPU - 1) {

                if
                :: GET_TAG(caches, cpu_id, adr) == adr ->
                    byte state = GET_STATE(caches, cpu_id, adr);
                    state_cnt[state]++;
                    // Cache line in shared or exclusive has to have the same data as main memory
                    assert((state != SHARED && state != EXCLUSIVE) || line.data == value);
                fi
            }

            assert(state_cnt[MODIFIED] <= 1);
            assert(state_cnt[EXCLUSIVE] <= 1);
            assert(state_cnt[SHARED] == 0 || (state_cnt[MODIFIED] == 0 && state_cnt[EXCLUSIVE] == 0));
        }
    }
}