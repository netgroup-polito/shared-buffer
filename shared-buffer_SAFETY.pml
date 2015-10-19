/* Shared Buffer Algorithm */

#define WAIT_FOR_SIGNAL			0		// the worker is sleeping
#define SIGNALED				1		// the worker is running
#define N 9								// buffer size
#define MASTER_PKT_THRESHOLD 9
#define WORKER_PKT_THRESHOLD 9
#define TIMEOUT					1
#define CONTINUE				0
#define isFull() (buffer_size == N-1)

/* Boolean variables representing the signs of the inequalities modelling the properties we want to check */
bit 	work_index_M_prod_index_inequality;	// W_prod_index < M_prod_index (in the initial state)
bit 	M_cons_index_work_index_inequality;	// consumer_index < W_prod_index (in the initial state)

/* Packets counters (used to check properties) */
byte 	from_master_to_worker_pkt_counter;	// counter for packets read from the master but not yet processed by the worker	
byte	from_worker_to_master_pkt_counter;	// counter for packets processed by the worker but not yet taken by the master

/* Variables shared between the master and the worker */
byte 	M_prod_index;		// assuming buffer size is less than 255
byte 	W_prod_index;		// ...idem
bit	worker_status;			// only two possible states for the worker: SIGNALED | WAIT_FOR_SIGNAL
byte 	buffer_size;		// actual buffer_size
bit	scheduling = 0;
bit	master_progress = 0;
bit	old_flag = 0;

/* Channel used to implement the synchronization between master and worker */
chan sem = [2] of {bit};

/* Channels used to realize the communication between the master and various functions */
chan writeDataIntoBuffer_ch = [0] of {bit};
chan checkForOldData_ch 	= [0] of {bit};
chan readDataFromBuffer_ch 	= [0] of {byte};	// The channel is used to pass (and to return) M_cons_index

active proctype master()
{
	/* Shared variables initialization */
	M_prod_index 	= 0;
	W_prod_index 	= 0;
	worker_status 	= WAIT_FOR_SIGNAL;
	buffer_size 	= 0;

	/* Private variables */
	byte 	i;
	byte 	M_cons_index;
	byte	temp_index;
	bool 	f_result;
	byte 	temp;
	M_cons_index 	= 0;

	d_step {
		from_master_to_worker_pkt_counter = 0;
		from_worker_to_master_pkt_counter = 0;
	
		work_index_M_prod_index_inequality = 0;
		M_cons_index_work_index_inequality = 0;
	}
		
	main_loop:
		i = 0;
		inner_loop:
			master_progress = 0;
			if
			:: (i < N);
				d_step
				{
					scheduling = 1;
					temp = M_prod_index;
					if
					:: (M_cons_index == 0);
						temp_index = N-1;
					:: else
						temp_index = M_cons_index-1;
					fi;
				}
				if
				:: (temp == temp_index);	// Buffer Full
					goto fine_for;
				:: else
					skip; 
				fi;
				/* Write data into the buffer */ 
				writeDataIntoBuffer_ch!1;
				writeDataIntoBuffer_ch?f_result;
			:: (1 == 1);
				/* Timeout expired */
				scheduling = 0;
				goto fine_for;
			fi;
			i = i + 1;
		goto inner_loop;
		fine_for:
		
		/* Read data from the buffer */
		readDataFromBuffer_ch!M_cons_index;
		readDataFromBuffer_ch?M_cons_index;
		
		/* Check for old Data */
		checkForOldData_ch!1;
		checkForOldData_ch?_;
		
	goto main_loop;
}

active proctype worker()
{
	/* Private variables */
	int 	pktCnt = 0;
	byte 	W_cons_index = 0;
	byte 	temp;
	
	worker_loop:
		sem?_;
		W_cons_index = W_prod_index;
		pktCnt = 0;
		worker_inner_loop:
			temp = M_prod_index;
			if
			:: (W_cons_index != temp);
				if
				:: (pktCnt == WORKER_PKT_THRESHOLD);
					pktCnt = 0;
					// Here we must verify if the W_prod_index has reverted to the beginning
					atomic {
						if
						:: (W_prod_index > W_cons_index);
							d_step {
								M_cons_index_work_index_inequality = 1-M_cons_index_work_index_inequality;
								work_index_M_prod_index_inequality = 1-work_index_M_prod_index_inequality; 
							}
						:: else skip;
						fi;
						W_prod_index = W_cons_index;
						/* Check assertions */
						if
						:: (work_index_M_prod_index_inequality == 0); assert (W_prod_index <= M_prod_index);
						:: (work_index_M_prod_index_inequality == 1); assert (W_prod_index >= M_prod_index);
						fi;
						/*******************/
					}
				:: else skip;
				fi;
				// process packet: NULL processing in this case
				// skip;
				//progress2: skip;
				d_step {
					/*
					 * Updating W_cons_index:
					 * Atomic execution (increment + modulo) is OK since W_cons_index is a private variable of the worker
					 */
					W_cons_index = (W_cons_index+1) % N;
					from_master_to_worker_pkt_counter--;
					from_worker_to_master_pkt_counter++;
					assert(from_master_to_worker_pkt_counter >= 0);
					assert(from_master_to_worker_pkt_counter < N);
				}
				pktCnt++;
			:: else goto fine_worker_inner_loop;
			fi;
		goto worker_inner_loop;
		
		
		fine_worker_inner_loop:
		// Here we must verify if the W_prod_index has reverted to the beginning
		atomic {
			if
			:: (W_prod_index > W_cons_index);
				M_cons_index_work_index_inequality = 1-M_cons_index_work_index_inequality;
				work_index_M_prod_index_inequality = 1-work_index_M_prod_index_inequality; 
			:: else 
				goto update_index;
			fi;
			update_index:
			W_prod_index = W_cons_index;
		}
		worker_status = WAIT_FOR_SIGNAL;
	goto worker_loop;
}

active proctype writeDataIntoBuffer()
{
	byte 	temp;
	byte 	result;
	bit		status;
	
	writeDataIntoBuffer_loop:
		writeDataIntoBuffer_ch?_;
		// Write the packet into the buffer
		/* A valid condition for livelock absence check is:
		 * more packets will always be written in the buffer
		 */
		 d_step{
			buffer_size++;
			master_progress = 1;
			from_master_to_worker_pkt_counter++;
			assert(from_master_to_worker_pkt_counter >= 0);
			assert(from_master_to_worker_pkt_counter < N);
		}
		/* Updating M_prod_index */
		temp = M_prod_index;
		temp++;
		if
		:: (temp == N);
			atomic {
				M_prod_index = 0;
				work_index_M_prod_index_inequality = 1-work_index_M_prod_index_inequality;
				/* Check assertions */
				if
				:: (work_index_M_prod_index_inequality == 0); assert (W_prod_index <= M_prod_index);
				:: (work_index_M_prod_index_inequality == 1); assert (W_prod_index >= M_prod_index);
				fi;
				/*******************/
			}
		:: else
			atomic {
				M_prod_index = temp;
				/* Check assertions */
				if
				:: (work_index_M_prod_index_inequality == 0); assert (W_prod_index <= M_prod_index);
				:: (work_index_M_prod_index_inequality == 1); assert (W_prod_index >= M_prod_index);
				fi;
				/*******************/
			}
		fi;
		/* Check whether to wake up the worker or not */
		status = worker_status;
		if
		:: (buffer_size > MASTER_PKT_THRESHOLD && status != SIGNALED);
			worker_status = SIGNALED;
			sem!1;
		:: else 
			skip;
		fi;
		result = 1;
		
		fine_writeDataIntoBuffer:
		writeDataIntoBuffer_ch!result;
	goto writeDataIntoBuffer_loop;
}

active proctype checkForOldData()
{
	bit 	status;
	
	checkForOldData_loop:
		checkForOldData_ch?_;
		/* Non-deterministic choice: are packets too old? */
		if
		:: (buffer_size > 0);
			status = worker_status;
			if
			:: (status != SIGNALED);
				if	// Are packets too old?
				:: (1 == 1);	// YES
					old_flag = 1;
					worker_status = SIGNALED;
					sem!1;
				:: (1 == 1);	// NO
					old_flag = 0;
				fi;
			:: else skip;
			fi;
		:: else skip;
		fi;
		checkForOldData_ch!1;	
	goto checkForOldData_loop;
}

/*
 * The function takes M_cons_index as input argument (through the channel)
 * and returns M_cons_index
 */
active proctype readDataFromBuffer()
{
	byte 	M_cons_index;
	byte 	temp;
	
	readDataFromBuffer_loop:
		readDataFromBuffer_ch?M_cons_index;
		readDataFromBuffer_while:
			/* Read data from buffer */
			temp = W_prod_index;
			if
			:: (M_cons_index != temp);
				// Consume the packet by decrementing buffer_size (variable used only by the master)
				buffer_size--;
				atomic {
					/* M_cons_index is a master's private variable */
					M_cons_index++;
					from_worker_to_master_pkt_counter--;
					if
					:: (M_cons_index == N);
						M_cons_index = 0;
						M_cons_index_work_index_inequality = 1-M_cons_index_work_index_inequality;
					:: else 
						goto readDataFromBuffer_while;
					fi;
					assert(from_worker_to_master_pkt_counter >= 0);
					assert(from_worker_to_master_pkt_counter < N);
					/* Check assertion */
					if
					:: (M_cons_index_work_index_inequality == 0); assert (M_cons_index <= W_prod_index);
					:: (M_cons_index_work_index_inequality == 1); assert (M_cons_index >= W_prod_index);
					fi;
					/*******************/
				}
			:: else goto fine_reading_data;
			fi;
		goto readDataFromBuffer_while;
		fine_reading_data:
		readDataFromBuffer_ch!M_cons_index;
	goto readDataFromBuffer_loop;
}
