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

// Cannot have () around statements, promela does not like that

#define ADDRESS_TO_CACHE_LINE(a) (a & (CACHE_SIZE - 1))
//#define GET_STATE(c, id, adr) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag & 3)
//#define SET_STATE(c, id, adr, st) c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag = ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag) & (~3)) | ((st) & 3)

//#define GET_TAG(c, id, adr) (c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag >> 2)
//#define SET_TAG(c, id, adr) c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag = ((c[id].lines[ADDRESS_TO_CACHE_LINE(adr)].tag) & 3) | (((adr) & 63) << 2)

#define GET_STATE(c, adr) (c.lines[ADDRESS_TO_CACHE_LINE(adr)].state)
#define SET_STATE(c, adr, st) c.lines[ADDRESS_TO_CACHE_LINE(adr)].state = (st)

#define GET_TAG(c, adr) (c.lines[ADDRESS_TO_CACHE_LINE(adr)].tag)
#define SET_TAG(c, adr) c.lines[ADDRESS_TO_CACHE_LINE(adr)].tag = (adr)

#define GET_VALUE(c, adr) (c.lines[ADDRESS_TO_CACHE_LINE(adr)].data)
#define SET_VALUE(c, adr, val) c.lines[ADDRESS_TO_CACHE_LINE(adr)].data = (val)

typedef cache_line {
    //// bits 0 to 1 are used for cache line state
    //// bits 2 to 7 are used for adress tag
    //byte tag;
    
    byte state;
    byte tag;
    byte data;
};

typedef cache {
    cache_line lines[CACHE_SIZE];
}

typedef cpu_op {
    bool read;
    byte address;
    byte value;
}

typedef bus_msg {
    byte type;
    byte address;
    byte data;
}

chan bus_c = [0] of {byte, bus_msg};
chan cpu_in[NUM_CPU] = [0] of {bus_msg};
chan cpu_out[NUM_CPU] = [0] of {bus_msg};

byte mem[MEM_SIZE];
cache caches[NUM_CPU];




inline update_required_bus_op() {
    // Apart from FLUSH, all messages will have the following settings
    req_msg.address = req.address;
    // Apart from FLUSH, all messages IGNORE data when sending
    req_msg.data = 0;
    
    // Bus operation needed based on the cache state and tag
    if 
    :: GET_TAG(caches[id], req.address) != req.address -> 
        if 
        :: GET_STATE(caches[id], req.address) == MODIFIED -> 
            req_msg.type = FLUSH;
            req_msg.address = GET_TAG(caches[id], req.address);
            req_msg.data = GET_VALUE(caches[id], req.address);
        :: else -> 
            if 
            :: req.read -> req_msg.type = READ;
            :: !req.read -> req_msg.type = READX;
            fi
        fi
    :: GET_TAG(caches[id], req.address) == req.address ->
        if 
        :: GET_STATE(caches[id], req.address) == INVALID -> 
            if 
            :: req.read -> req_msg.type = READ;
            :: !req.read -> req_msg.type = READX;
            fi
        :: GET_STATE(caches[id], req.address) == SHARED -> 
            if
            :: req.read -> req_msg.type = NONE;
            :: !req.read -> req_msg.type = UPGRD;
            fi 
        :: GET_STATE(caches[id], req.address) == EXCLUSIVE -> req_msg.type = NONE;
        :: GET_STATE(caches[id], req.address) == MODIFIED -> req_msg.type = NONE;
        fi
    fi
}

inline generate_request() {
    if 
    :: req.read = true;
    :: req.read = false;
    fi

    if 
    :: req.address = 0;
    :: req.address = 1;
    :: req.address = 2;
    :: req.address = 3;
    fi
    // Value is ignored when reading.
    if 
    :: req.value = 0;
    :: req.value = 1;
    fi

    update_required_bus_op(); 
}

inline modify_cache() {
    SET_STATE(caches[id], req.address, MODIFIED);
    SET_STATE(local_cache, req.address, MODIFIED);
    SET_VALUE(caches[id], req.address, req.value);
}

inline read_from_cache() {
    assert(GET_STATE(caches[id], req.address) == MODIFIED || GET_VALUE(caches[id], req.address) == mem[req.address]);
}

inline update_cache_own_op() {
    if 
    :: req_msg.type == READ  ->
        SET_STATE(caches[id], req_msg.address, SHARED);
        SET_STATE(local_cache, req_msg.address, SHARED);
        SET_TAG(caches[id], req_msg.address);
        SET_TAG(local_cache, req_msg.address);
        SET_VALUE(caches[id], req_msg.address, req_msg.data);
    :: req_msg.type == READX ->
        SET_STATE(caches[id], req_msg.address, EXCLUSIVE);
        SET_STATE(local_cache, req_msg.address, EXCLUSIVE);
        SET_TAG(caches[id], req_msg.address);
        SET_TAG(local_cache, req_msg.address);
        SET_VALUE(caches[id], req_msg.address, req_msg.data);
    :: req_msg.type == UPGRD -> 
        SET_STATE(caches[id], req_msg.address, EXCLUSIVE);
        SET_STATE(local_cache, req_msg.address, EXCLUSIVE);
    :: req_msg.type == FLUSH -> 
        SET_STATE(caches[id], req_msg.address, SHARED);
        SET_STATE(local_cache, req_msg.address, SHARED);
    fi
}

inline update_cache_snooped_op() {
    reply_msg.type = NONE;
    reply_msg.address = snoop_msg.address;
    reply_msg.data = snoop_msg.data;

    // If the address is stored in our cache
    if
    :: GET_TAG(caches[id], snoop_msg.address) == snoop_msg.address && GET_STATE(caches[id], snoop_msg.address) != INVALID ->
        
        assert(snoop_msg.type != FLUSH); // FLUSH should never happen while we have the cache line in valid state
        
        if
        :: GET_STATE(caches[id], snoop_msg.address) == MODIFIED -> //FLUSH
            reply_msg.type = FLUSH;
            reply_msg.address = snoop_msg.address;
            reply_msg.data = GET_VALUE(caches[id], snoop_msg.address);
        :: else -> skip;
        fi
        
        if
        :: snoop_msg.type == READ -> 
            SET_STATE(caches[id], snoop_msg.address, SHARED);
            SET_STATE(local_cache, snoop_msg.address, SHARED);
        :: snoop_msg.type == READX -> 
            SET_STATE(caches[id], snoop_msg.address, INVALID);
            SET_STATE(local_cache, snoop_msg.address, INVALID);
        :: snoop_msg.type == UPGRD -> 
            SET_STATE(caches[id], snoop_msg.address, INVALID);
            SET_STATE(local_cache, snoop_msg.address, INVALID);
        fi
    :: else -> skip;
    fi    
}

inline execute_in_cache() {
    assert(req_msg.type == NONE);
    if
    :: req.read -> read_from_cache();
    :: !req.read -> modify_cache();
    fi   
}

/*
* Changes the state of the cpu cache based on the snooped updates.
* Updates the cpu action based on the new state of the cache.
* Replies to the bus so that the other cpu can proceed.
*/
inline snoop() {
    update_cache_snooped_op();
    update_required_bus_op();
    cpu_out[id] ! reply_msg;
}

proctype cpu(byte id) {
    //Read or write
    cpu_op req;
    cache local_cache;

    bus_msg req_msg;

    // Used when snooping on the bus
    bus_msg snoop_msg;

    // Used when replying to the snooping on the bus
    bus_msg reply_msg;
    generate_request();

    do
        // Can execute the action using cache
        :: req_msg.type == NONE ->
            if 
            // Listening on the bus for other cpu communications
            :: cpu_in[id] ? snoop_msg -> 
                // Change our request based on the updates and reply
                snoop();
            :: req_msg.type == NONE ->  // try execute request, do nothing if needs com
                execute_in_cache();
                generate_request(); //Generate new request
            fi    
        // We have to communicate to change the cache state, so that we can execute the action
        :: req_msg.type != NONE ->
            if 
            // The communication on the bus to enable us to execute our action
            :: bus_c ! id, req_msg -> 
                // Models cpu setting address and type on the bus address and control lines
                // and receiving data in the next cycle on the data lines
                // For FLUSH message, even the data lines are set by cpu
                cpu_in[id] ? req_msg;
                update_cache_own_op();
                update_required_bus_op();
            // Listening on the bus for other cpu communications
            :: cpu_in[id] ? snoop_msg ->
                // Change our request based on the updates and reply
                snoop();
            fi
    od
}

active proctype bus() {
    byte i;
    byte cpu_id;
    bus_msg req_msg;
    bus_msg reply_msg;
    do
        ::bus_c ? cpu_id, req_msg -> 
            assert(req_msg.type != NONE);

            for (i : 0 .. NUM_CPU - 1) {
                if 
                :: i != cpu_id 
                    cpu_in[i] ! req_msg;
                    // Has to be atomic so that we can check that on read from cache,
                    // the cache contains the same value as memory
                    atomic {
                        cpu_out[i] ? reply_msg;
                                    
                        assert(reply_msg.type == NONE || reply_msg.type == FLUSH);
                        assert(!(req_msg.type == FLUSH && reply_msg.type == FLUSH));
                        assert(reply_msg.address == req_msg.address);

                        if 
                        :: reply_msg.type == NONE -> skip;
                        :: reply_msg.type == FLUSH -> mem[reply_msg.address] = reply_msg.data; 
                        fi
                    }
                    
                :: else -> skip;
                fi
            }

            if 
            :: req_msg.type == FLUSH -> mem[req_msg.address] = req_msg.data;
            :: else -> skip;
            fi
            cpu_in[cpu_id] ! req_msg.type, req_msg.address, mem[req_msg.address]
    od
}

active proctype cache_state_check() {
    byte adr;
    byte cpu_id;
    byte state_cnt[4];
    do
    :: skip ->
        d_step{
            for (adr: 0 .. MEM_SIZE - 1) {
                state_cnt[0] = 0;
                state_cnt[1] = 0;
                state_cnt[2] = 0;
                state_cnt[3] = 0;
                for (cpu_id: 0 .. NUM_CPU - 1) {

                    if
                    :: GET_TAG(caches[cpu_id], adr) == adr ->
                        state_cnt[GET_STATE(caches[cpu_id], adr)]++;
                        // Cache line in shared or exclusive has to have the same data as main memory
                        assert((GET_STATE(caches[cpu_id], adr) != SHARED && GET_STATE(caches[cpu_id], adr) != EXCLUSIVE) || 
                                GET_VALUE(caches[cpu_id], adr) == mem[adr]);
                    :: else -> skip;
                    fi
                }

                assert(state_cnt[MODIFIED] <= 1);
                assert(state_cnt[EXCLUSIVE] <= 1);
                assert(!(state_cnt[MODIFIED] > 0 && state_cnt[EXCLUSIVE] > 0));
                assert(state_cnt[SHARED] == 0 || (state_cnt[MODIFIED] == 0 && state_cnt[EXCLUSIVE] == 0));
            }
        }
    od
}

init {
    byte id;
    for (id: 0 .. NUM_CPU - 1) {
        run cpu(id);
    }
}