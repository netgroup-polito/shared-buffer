# Shared Buffer model
Algorithm to efficiently move pkts between the vSwitch and the VNF.
In this repository we include the Promela code used to model and verify our algorithm againts a set of properties defined in our paper.

## Prerequisites
In order to reproduce the obtained results you need the following software already installed on your (Linux) system:
  - Spin 6.x (available at http://spinroot.com/spin/whatispin.html). In the following we assume spin is in the PATH;
  - Yacc and LeX (they can be installed on ubuntu by typing "sudo apt-get install byacc flex" on the console)

In this repo you can find:
  - shared-buffer_SAFETY.pml -> the model of the buffer and the SAFETY properties we verified on it
  - shared-buffer_LIVENESS.pml -> the model of the buffer and the LIVENESS properties we verified on it
  - run.sh -> a script that can be used to verify both LIVENESS and SAFETY properties. At the beginning of the script you can edit and specify a range of values for the different model parameters. The script will test all the possible configurations.

## Run
In order to run the verification with Spin, you just need to type the following command:
```sh
$ ./run.sh {safety|ltl}
```
