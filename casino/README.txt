This folder shows a verified Whiley implementation of a simple Casino contract.

The contract is described in the paper:

Ahrendt W. et al. (2019) Verification of Smart Contract Business Logic. In: Hojjat H., Massink M. (eds) Fundamentals of Software Engineering. FSEN 2019. Lecture Notes in Computer Science, vol 11761. Springer, Cham. https://doi.org/10.1007/978-3-030-31517-7_16

They translated the original Solidity contract into Java+JML and verified two methods using the KEY tool.
The source code for their Java translation of a contract is here: https://github.com/raulpardo/casino-contract-java-solidity.

This Whiley version can verify all the methods automatically, using the Boogie verifier.
However, we verify only the success path of each method, not the errors paths that cause the contract to backtrack and leave the state unchanged.

