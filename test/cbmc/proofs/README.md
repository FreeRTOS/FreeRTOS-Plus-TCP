This directory contains the proofs checked by CBMC.   For each entry point of FreeRTOS-Plus-TCP tested, there is a directory that contains the test harness and cbmc configuration information needed to check the proof.

### To run the proofs yourselves

#### Install CBMC
- Install CBMC using the instruction found on the [diffblue github](https://github.com/diffblue/cbmc).
- FOR UBUNTU, you can download the source from the [diffblue github](https://github.com/diffblue/cbmc) and run the below commands:
  - After going into the downloaded/cloned repo directory, run `make -C src minisat2-download`.
  - Run `make -C src -j8 CXX=g++-6`

#### Download the FreeRTOS-Plus-TCP repository
- See the instructions for cloning this repository in the [README.md](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP#cloning-this-repository).

#### Prepare the proofs
- Go to the `test/cbmc/proofs` directory (most probably you are in this directory right now).
- Run `python3 prepare.py`. Note: It is important that you use `python3`.

#### Run the proofs
- Select a proof to run. We shall choose `ARP/ARPAgeCache` as an example.
- Go to the proof directory (`ARP/ARPAgeCache`).
- Run `make cbmc`.
- Run `make report`. This command should generate an HTML file which can be opened in a web-browser and can be traversed like a web page.
