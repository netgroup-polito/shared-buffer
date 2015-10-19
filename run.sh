#!/bin/bash

readonly OUTPUT_PAN="output_pan.txt"
readonly MAIN_DIR="verifications"

readonly MIN_MASTER_THRESHOLD=1
readonly MAX_MASTER_THRESHOLD=8

readonly MIN_WORKER_THRESHOLD=1
readonly MAX_WORKER_THRESHOLD=8

readonly MIN_BUFFER_SIZE=2
readonly MAX_BUFFER_SIZE=8

# trap ctrl-c and call exit_handler()
trap exit_handler INT

function exit_handler() {
	if [ -e "$OUTPUT_PAN" ]
	then
		printf "[ERROR] Verification aborted\n" >> "$OUTPUT_PAN";
	fi
	printf "\n***\nAborted!\n***\n";
	clean
	run=false;
}

function clean() {
	rm -f temp_f
	rm -f out
	rm -f out2
	rm -f out3
}

if [[ $# != 1 ]] ; then
	printf "[ERROR] Wrong number of parameters.\nUsage: ./run LTL|SAFETY\nExiting.\n";
	exit -1;
fi

if [[ $1 != 'SAFETY' && $1 != 'LTL' && $1 != 'safety' && $1 != 'ltl' ]] ; then
	printf "[ERROR] Invalid parameter.\n[ERROR] Valid parameters are: LTL|SAFETY\n";
	exit -2;	
fi

if [[ $1 == 'LTL' || $1 == 'ltl' ]]
then
	MODEL="shared-buffer_LIVENESS.pml"		# Use this for ltl properties
else
	MODEL="shared-buffer_SAFETY.pml"		# Use this for safety properties
fi

i=1
run=true
rm -f $OUTPUT_PAN
rm -f -R $MAIN_DIR
mkdir $MAIN_DIR
touch $OUTPUT_PAN

NUMBER_OF_TESTS=$(( (MAX_BUFFER_SIZE - MIN_BUFFER_SIZE + 1) * (MAX_WORKER_THRESHOLD - MIN_WORKER_THRESHOLD + 1) * (MAX_MASTER_THRESHOLD - MIN_MASTER_THRESHOLD + 1) ))
printf "\n+++Number of tests scheduled=$NUMBER_OF_TESTS\n+++Press CTRL-C to stop execution\n\n\n";

for MASTER_PKT_THRESHOLD in $(seq $MIN_MASTER_THRESHOLD $MAX_MASTER_THRESHOLD)
do
	for WORKER_PKT_THRESHOLD in $(seq $MIN_WORKER_THRESHOLD $MAX_WORKER_THRESHOLD)
	do
		for BUFFER_SIZE in $(seq $MIN_BUFFER_SIZE $MAX_BUFFER_SIZE)
		do
			if [[ $run != true ]]
			then
				exit
			fi
			
			printf "************************************************\n" >> "$OUTPUT_PAN";
			printf "Model checking results with following values:\n" >> "$OUTPUT_PAN";
			printf "\tBUFFER_SIZE=$BUFFER_SIZE\n" >> "$OUTPUT_PAN";
			printf "\tMASTER_PKT_THRESHOLD=$MASTER_PKT_THRESHOLD\n" >> "$OUTPUT_PAN";
			printf "\tWORKER_PKT_THRESHOLD=$WORKER_PKT_THRESHOLD\n" >> "$OUTPUT_PAN";
			printf "RESULTS:\n" >> "$OUTPUT_PAN";
			
			if [[ ($WORKER_PKT_THRESHOLD -gt $BUFFER_SIZE) || ($MASTER_PKT_THRESHOLD -gt $BUFFER_SIZE) ]]
			then
				printf "Test $i/$NUMBER_OF_TESTS skipped!\n";
				printf "Test $i/$NUMBER_OF_TESTS skipped!\n" >> "$OUTPUT_PAN";
				let i+=1;
				continue;
			fi
			
			# Generate the model source file
			FILE_PML="temp"$i".pml"
			sed "1,15s/#define N 9/#define N $BUFFER_SIZE/g" $MODEL > out;
			sed "1,15s/#define MASTER_PKT_THRESHOLD 9/#define MASTER_PKT_THRESHOLD $MASTER_PKT_THRESHOLD/g" out > out2;
			sed "1,15s/#define WORKER_PKT_THRESHOLD 9/#define WORKER_PKT_THRESHOLD $WORKER_PKT_THRESHOLD/g" out2 > out3;
			cat out3 > "$MAIN_DIR/$FILE_PML";
			printf "\tMODEL_NAME=$FILE_PML\n" >> "$OUTPUT_PAN";
			
			# Generate the model checker code
			spin -a out3;
			rc=$?
			if [[ $rc != 0 ]] ; then
				printf "[SPIN ERROR] Unable to generate model checker\n";
				printf "Error $rc\n";
				exit $rc;
			else
				printf "Model checker generated!\n";
			fi

			# Compile the model checker
			if [[ $1 == 'LTL' || $1 == 'ltl' ]]
			then
				# Compilation in case of non-progress cycle
				gcc -DNOREDUCE -DNFAIR=3 -o pan pan.c
			else
				# Compilation in case of safety properties only
				gcc -o2 -DSAFETY -o pan pan.c
			fi
			rc=$?
			if [[ $rc != 0 ]] ; then
				printf "[GCC ERROR] Unable to compile model checker\n";
				exit $rc;
			else
				printf "Model checker compiled!\n";
			fi

			# Execute model checking
			rm -f temp_f;
			touch temp_f;
			printf "\tPAN Execution OUTPUT:\n" >> "$OUTPUT_PAN";
			# -X print all stderr output onto stdout instead
			# -mN set max search depth to N steps (default N=10000)
			# -l find non progress cycle
			# -f enable weak fairness
			# -i find minimum example
			if [[ $1 == 'LTL' || $1 == 'ltl' ]]
			then
				# Execution in case of ltl properties
				./pan -m100000000 -a -f >> temp_f;
			else
				# Execution in case of safety properties only
				./pan -m100000000 -X >> temp_f;
			fi
			rc=$?
			if [[ -e temp_f ]]
			then
				#cat temp_f | grep "errors" >> "$OUTPUT_PAN";
				sed '/[mM]emory/d' temp_f >> "$OUTPUT_PAN";
				if [[ $rc == 0 ]] ; then
					printf "Test $i/$NUMBER_OF_TESTS completed!\n";
					printf "Test $i/$NUMBER_OF_TESTS completed!\n" >> "$OUTPUT_PAN";
				fi
			fi
			printf "************************************************\n" >> "$OUTPUT_PAN";
			let i+=1;
			clean
		done
	done
done
