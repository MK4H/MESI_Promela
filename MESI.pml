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

typedef cache_line_t {
    //// bits 0 to 1 are used for cache line state
    //// bits 2 to 7 are used for adress tag
    //byte tag;
    
    byte state;
    byte tag;
    byte data;
};

typedef cache_t {
    cache_line_t lines[CACHE_SIZE];
}

typedef cpu_op_t {
    bool read;
    byte address;
    byte value;
}

typedef bus_msg_t {
    byte type;
    byte address;
}

typedef bus_t {
    bool locked;
    byte msg_type;
    byte address;
    bool snooped;
}

byte mem[MEM_SIZE];
cache_t caches[NUM_CPU];
bus_t bus;




inline update_required_bus_op() {
    // Apart from FLUSH, all messages will have the following settings
    req_msg.address = req.address;
    
    // Bus operation needed based on the cache state and tag
    if 
    :: GET_TAG(caches[id], req.address) != req.address -> 
        if 
        :: GET_STATE(caches[id], req.address) == MODIFIED ->
            printf("FLUSHING");
            req_msg.type = FLUSH;
            req_msg.address = GET_TAG(caches[id], req.address);
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
    atomic {
        SET_STATE(caches[id], req.address, MODIFIED);
        SET_VALUE(caches[id], req.address, req.value);
    }
    printf("CPU %d setting cache to %d by cache write", _pid, GET_STATE(caches[id], req_msg.address)); 
}

inline read_from_cache() {
    assert(GET_STATE(caches[id], req.address) == MODIFIED || GET_VALUE(caches[id], req.address) == mem[req.address]);
}

inline execute_bus_op() {
    if 
    :: req_msg.type == READ  ->
        atomic {
            SET_STATE(caches[id], req_msg.address, SHARED);
            SET_TAG(caches[id], req_msg.address);
            SET_VALUE(caches[id], req_msg.address, mem[req_msg.address]);
        }
    :: req_msg.type == READX ->
        atomic {
            SET_STATE(caches[id], req_msg.address, EXCLUSIVE);
            SET_TAG(caches[id], req_msg.address);
            SET_VALUE(caches[id], req_msg.address, mem[req_msg.address]);
        }
    :: req_msg.type == UPGRD ->
        SET_STATE(caches[id], req_msg.address, EXCLUSIVE);
    :: req_msg.type == FLUSH -> 
        printf("Writing value \"%d\" into mem[%d]\n", GET_VALUE(caches[id], bus.address), bus.address);
        // Has to be atomic so that the following invariant is true:
        // Cache in SHARED or EXCLUSIVE state has the same value as memory
        atomic {
            SET_STATE(caches[id], req_msg.address, SHARED);
            mem[req_msg.address] = GET_VALUE(caches[id], req_msg.address);
        }
    fi
    printf("CPU %d setting cache to %d by bus op\n", _pid, GET_STATE(caches[id], req_msg.address)); 
}

inline execute_in_cache() {
    assert(req_msg.type == NONE);
progress:
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
    // If the address is stored in our cache
    if
    :: GET_TAG(caches[id], bus.address) == bus.address && GET_STATE(caches[id], bus.address) != INVALID ->
        
        assert(bus.msg_type != FLUSH); // FLUSH should never happen while we have the cache line in valid state
        
        if
        :: GET_STATE(caches[id], bus.address) == MODIFIED -> //FLUSH
            printf("Writing value \"%d\" into mem[%d]\n", GET_VALUE(caches[id], bus.address), bus.address);
            mem[bus.address] = GET_VALUE(caches[id], bus.address);
        :: else -> skip;
        fi
        
        if
        :: bus.msg_type == READ -> SET_STATE(caches[id], bus.address, SHARED);
        :: bus.msg_type == READX -> SET_STATE(caches[id], bus.address, INVALID);
        :: bus.msg_type == UPGRD -> SET_STATE(caches[id], bus.address, INVALID);
        fi
        printf("CPU %d setting cache to %d by snooping\n", _pid, GET_STATE(caches[id], req_msg.address)); 
    :: else -> skip;
    fi

    update_required_bus_op();
}

proctype cpu(byte id) {

    cpu_op_t req;

    bus_msg_t req_msg;

    generate_request();

    do
        // Can execute the action using cache
        :: req_msg.type == NONE ->
            //Execute the operation while we can
            execute_in_cache();
            generate_request(); //Generate new request
            if 
            // Listening on the bus for other cpu communications
            :: bus.locked && !bus.snooped -> 
                // Change our request based on the updates and reply
                snoop();
                bus.snooped = true;
            :: else -> skip;
            fi    
        // We have to communicate to change the cache state, so that we can execute the action
        :: req_msg.type != NONE ->
            if 
            // The communication on the bus to enable us to execute our action
            :: atomic {
                    !bus.locked;
                    bus.locked = true;
                    bus.msg_type = req_msg.type;
                    bus.address = req_msg.address;
                } 
                bus.snooped;

                execute_bus_op();
                update_required_bus_op();
                atomic {
                    bus.snooped = false;
                    bus.locked = false;
                }
            // Listening on the bus for other cpu communications
            // If we already snooped, byt the bus is still locked, we will block here, because there is nothing we can do
            :: bus.locked && !bus.snooped;
                // Change our request based on the updates and reply
                snoop();
                bus.snooped = true;
            fi
    od
}


init {
    atomic {
        run cpu(0);
        run cpu(1);
    }
}

/* active proctype cache_state_check() {
    d_step{ 
        byte adr;
        byte cpu_id;
        byte state_cnt[4]
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
}
 */

// References to local variables do not work at all with member access
// Additionally, they do not work with partial order reduction during verification
// ltl test { [] ((cpu[0]:req).read == false) }

#define cpu0ctag (caches[0].lines[0].tag)
#define cpu1ctag (caches[1].lines[0].tag)

#define cpu0cstate (caches[0].lines[0].state)
#define cpu1cstate (caches[1].lines[0].state)

#define cpu0cval (caches[0].lines[0].data)
#define cpu1cval (caches[1].lines[0].data)

#define mem_at_cpu0_cache (mem[caches[0].lines[0].tag])
#define mem_at_cpu1_cache (mem[caches[1].lines[0].tag])

ltl single_modified { [] ((cpu0ctag != cpu1ctag) || 
                            (((cpu0cstate == MODIFIED) -> (cpu1cstate == INVALID)) && 
                            ((cpu1cstate == MODIFIED) -> (cpu0cstate == INVALID)))) }


ltl single_exclusive { [] ((cpu0ctag != cpu1ctag) || 
                            (((cpu0cstate == EXCLUSIVE) -> (cpu1cstate == INVALID)) && 
                            ((cpu1cstate == EXCLUSIVE) -> (cpu0cstate == INVALID)))) }


ltl sh_ex_mem_value { [] ((((cpu0cstate == SHARED) || (cpu0cstate == EXCLUSIVE)) ->
                            (cpu0cval == mem_at_cpu0_cache)) &&
                          (((cpu1cstate == SHARED) || (cpu1cstate == EXCLUSIVE)) ->
                            (cpu1cval == mem_at_cpu1_cache))) }
