## Verification Overview
The current directory contains Certora's formal verification of AAVE's V2 AStETH.
In this directory you will find three subdirectories:

1. specs - Contains all the specification files that were written by Certora and AAVE's community for the AStETH. We have created two spec files, `AStETH_summerizations.spec`, `AStETH.spec`, the first is used to simplify computations by summarizing the relevant function in order to fix the rebasing index. The choice for this summarizations relies on the contracts rebasing computation.
and the second spec file inherits AStETH_summerizations.spec and holds all the rules to verify AStETH contract with respect to those summarizations.

2. scripts - Contains all the necessary run script to execute the spec files on the Certora Prover. These script composed of a run command of Certora Prover, contracts to take into account in the verification context, declaration of the compiler and a set of additional settings.

3. harness - Contains all the inheriting contracts that add/simplify functionalities to the original contract. You will also find a set of symbolic and dummy implementations of external contracts on which the executors rely.
These harnesses, i.e. extensions/simplifications, are necessary to run the verifications. Assumptions and under-approximations are also done in a few places, in order to supply partial coverage where full coverage is not achievable.
One harness worth explaining is the SymbolicLendingPool contract that were created in order to simulate the Lending Pool which interacts with the Token. 

</br>

---

## Running Instructions
To run a verification job:

1. Open terminal and `cd` your way to the main AAVE repository.

2. Run the script you'd like to get results for:
    ```
    sh certora/scripts/verifyAStETH.sh
    ```

</br>