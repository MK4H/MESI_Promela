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
#define INVAL 0
#define READ  1
#define READX 2
#define UPGRD 3
#define FLUSH 4

#define ADDRESS_TO_CACHE_LINE(a) (a & (CACHE_SIZE - 1))
#define GET_STATE(t) (t & 3)
#define SET_STATE(s,t) (t = ((t) & (~3)) | ((s) & 3))
#define GET_TAG(t) (t >> 2)
#define SET_TAG(a, t) ((t) = ((t) & 3) | (((a) & 8) << 2))

typedef cache_line {
    // bits 0 to 1 are used for cache line state
    // bits 2 to 5 are used for adress tag 
    byte tag;
    byte data;
};

chan bus_c = [0] of {byte, byte, byte, byte};
chan cpu_in[NUM_CPU] = [0] of {byte, byte};
chan cpu_out[NUM_CPU] = [0] of {bool, byte};

byte mem[MEM_SIZE];

proctype bus() {
    byte i;
    byte cpu_id;
    byte msg_type;
    byte address;
    byte data;
    do
        ::bus_c ? cpu_id, msg_type, address, data  -> 
            if 
            :: msg_type == READ -> 
                for (i : 0 .. NUM_CPU - 1) {
                    if (i != cpu_id) {
                        cpu_c[i] ! msg_type, address;
                    }
                }
            :: msg_type == UPGRD ->
                for (i : 0 .. NUM_CPU - 1) {
                    if (i != cpu_id) {
                        cpu_c[i] ! msg_type, address;
                    }
                }
            :: msg_type == FLUSH -> 
                for (i : 0 .. NUM_CPU - 1) {
                    if (i != cpu_id) {
                        cpu_c[i] ! msg_type, address;
                    }
                }
            fi
    od
}

inline snoop(p_cache, p_message, p_address, p_value) {
    if 
    :: p_message == READ ->
        if
        ::
        fi
    :: p_message == READX ->
    :: p_message == UPGRD ->
    :: p_message == FLUSH ->
    fi
}

proctype cpu() {
    cache_line cache[CACHE_SIZE];

    //Read or write
    bool read;
    byte adress;

    do
        :: skip ->
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
            
            byte cache_state = GET_STATE(cache[ADDRESS_TO_CACHE_LINE(address)].tag);
            byte cache_tag = GET_TAG(cache[ADDRESS_TO_CACHE_LINE(address)].tag);

            byte bus_op;

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
                    :: read -> assert(cache[ADDRESS_TO_CACHE_LINE(address)].data == value);
                    :: else -> 
                        bus_op = UPGRD;
                        //bus_c ! UPGRD, address;
                        //SET_STATE(MODIFIED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                        //cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
                    fi 
                :: cache_state == EXCLUSIVE ->
                    if
                    :: read -> assert(cache[ADDRESS_TO_CACHE_LINE(address)].data == value);
                    :: else -> 
                        SET_STATE(MODIFIED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                        cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
                    fi 
                :: cache_state == MODIFIED -> 
                    if 
                    :: read -> assert(cache[ADDRESS_TO_CACHE_LINE(address)].data == value);
                    :: else -> cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
                    fi
                fi
            fi

            /*
            TODO: On initialization generate the request we want to do
            Then go into a cycle, where we try to send on the bus, if we have
            a request that needs it, or we just listen or do request if we have
            request that don't need to communicate
            
            */
            //THIS IS THE NEWEST PART, TRY TO REDO THE THING UNDERNEATH AND ABOVE INTO THIS
            if 
            :: need_com && bus_c ! ... -> //DO THE COMMUNICATION
            :: else ->
                if 
                :: cpu_in ? ... -> // read from the bus, change the request based on the updates
                :: have_request -> // try execute request, do nothing if needs com
                :: else -> // generate new request
            fi

            //TODO: Check if bus_op is even needed
            if 
            :: bus_c ! bus_op, address, value -> 
                if 
                :: bus_op == READ ->
                    cpu_in ! from_mem, rcv_value;
                    cache[ADDRESS_TO_CACHE_LINE(address)].data = rcv_value;
                    SET_TAG(address, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                    if 
                    :: from_mem -> SET_STATE(EXCLUSIVE, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                    :: !from_mem -> SET_STATE(SHARED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                    fi
                :: bus_op == READX ->
                    cpu_in ! from_mem, rcv_value;
                    cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
                    SET_TAG(address, cache[ADDRESS_TO_CACHE_LINE(address)].tag);      
                    SET_STATE(MODIFIED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                :: bus_op == UPGRD ->
                    //Ignore, just to synchronize with the bus
                    cpu_in ! from_mem, rcv_value;
                    cache[ADDRESS_TO_CACHE_LINE(address)].data = value;
                    SET_TAG(address, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                    SET_STATE(MODIFIED, cache[ADDRESS_TO_CACHE_LINE(address)].tag);
                :: bus_op == FLUSH -> //TODO: THIS
                fi
            //SNOOPING
            :: cpu_in ? mes_type, value ->
                if 
                :: mes_type == READ && value == cache_tag 
            fi
    od
}