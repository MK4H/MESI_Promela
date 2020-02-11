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
#define GET_STATE(t) (t & 3)
#define SET_STATE(s,t) (t = ((t) & (~3)) | ((s) & 3))
#define GET_TAG(t) (t >> 2)
#define SET_TAG(a, t) ((t) = ((t) & 3) | (((a) & 63) << 2))

typedef cache_line {
    // bits 0 to 1 are used for cache line state
    // bits 2 to 7 are used for adress tag 
    byte tag;
    byte data;
};

typedef cache {
    cache_line line[CACHE_SIZE];
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
    cache_state = GET_STATE(cache[ADDRESS_TO_CACHE_LINE(address)].tag);
    cache_tag = GET_TAG(cache[ADDRESS_TO_CACHE_LINE(address)].tag); 

    update_required_bus_op(); 
}

inline modify_cache() {
    SET_STATE(MODIFIED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
    cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
}

inline read_from_cache() {
    assert(cache[ADDRESS_TO_CACHE_LINE(address)].data == value);
}

inline update_cache_own_op() {
    if 
    :: bus_op == READ  ->
        SET_STATE(SHARED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
        cache[ADDRESS_TO_CACHE_LINE(address)].data = data;
    :: bus_op == READX ->
        SET_STATE(EXCLUSIVE, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
        cache[ADDRESS_TO_CACHE_LINE(address)].data = data;
    :: bus_op == UPGRD -> SET_STATE(EXCLUSIVE, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
    :: bus_op == FLUSH -> SET_STATE(SHARED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
    fi
}

inline update_cache_other_op() {
    // If the address is stored in our cache
    if
    :: GET_TAG(cache[ADDRESS_TO_CACHE_LINE(snp_address)].tag) == snp_address && snp_state != INVALID ->
        if
        :: snp_state == MODIFIED -> //FLUSH
        
        assert(snp_bus_op != FLUSH); // FLUSH should never happen while we have the cache line in valid state

        if
        :: snp_bus_op == READ -> SET_STATE(SHARED, cache[ADDRESS_TO_CACHE_LINE(snp_address)].tag);
        :: snp_bus_op == READX -> SET_STATE(INVALID, cache[ADDRESS_TO_CACHE_LINE(snp_address));
        :: snp_bus_op == UPGRD -> SET_STATE(INVALID, cache[ADDRESS_TO_CACHE_LINE(snp_address));
        fi
    :: else -> skip;
    fi    
}

proctype cpu(byte id) {
    cache_line cache[CACHE_SIZE];

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
            :: bus_op != NONE && bus_c ! id, bus_op, address, data -> //DO THE COMMUNICATION
                cpu_in ? bus_op, address, data;
                update_cache_value();
                update_required_bus_op();
                //TODO: Maybe execute the request
            :: else ->
                byte snp_bus_op;
                byte snp_address;
                byte snp_data;
                byte snp_state;
                if 
                :: cpu_in ? snp_bus_op, snp_address, snp_data -> // snoop from the bus, change the request based on the updates
                    snp_state = GET_STATE(cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                    update_cache_state();
                    update_required_bus_op();
                :: bus_op == NONE ->  // try execute request, do nothing if needs com
                    if
                    :: read -> read_from_cache();
                    :: !read -> modify_cache();
                    fi   
                    generate_request(); //Generate new request
                :: else -> skip; //Try to acquire the bus and snoop some more 
                fi 
            fi
    od
}