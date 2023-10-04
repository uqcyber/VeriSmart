# VeriSmart
Machine-checked formal verification of smart contracts for various blockchains.
## Verification of Smart Contracts for Blockchain Applications

This project is to explore techniques for verifying smart contracts.


Folders::
 * EVM_Vale: using Vale and Z3 to verify EVM bytecode programs
   Case studies: casino and a token
 * casino: The simple casino case study verified using Whiley.
   See: https://arxiv.org/abs/2106.14457
 * notes: for any notes (usually *.txt or *.md).
 * papers: for papers about this project.


## EVM_Vale

Installing F* so that printing is enabled:
1.  Download this version of F* "https://github.com/FStarLang/FStar/releases/tag/v2022.05.06"
2.  Place in vale repository in directory tools
3.  Rename folder placed in tools from "fstar" to "FStar"
4.  Download opam
5.  Navigate to vale home
6.  Install OCaml 4.12.1 (opam switch create 4.12.1) 
7.  Install dependencies listed on F* INSTALL.md "opam install ocamlfind batteries stdint zarith ppx_deriving_yojson pprint 'ppxlib>=0.22.0' ocaml-compiler-libs"
8.  Run "eval $(opam env)"
9.  Run "export FSTAR_HOME=~/PATH TO VALE/tools/FStar" 
10. Run "make -C ulib install-fstarlib"
11. Run "make -C ulib/ml"	
12. Run "make -C examples/hello hello" this should work

Printing Vale PowerPC architecture examples:
1. sudo apt-get install -y gcc-powerpc64le-linux-gnu
2. sudo apt-get install qemu-user
3. eval $(opam env)

Vale and EVM:

To get started, I recommend reading up on EVM. This medium article https://medium.com/swlh/getting-deep-into-evm-how-ethereum-works-backstage-ab6ad9c0d0bf is quite helpful to get a good overview of EVM. 

A quick reference for EVM opcodes is this https://ethereum.org/en/developers/docs/evm/opcodes/ , and the ethereum yellow paper https://ethereum.github.io/yellowpaper/paper.pdf or Grischenko et al. https://arxiv.org/pdf/1802.08660.pdf for the semantics of what those opcodes do at the end of the papers. The yellow paper is NOT completely semantically accurate, but for our purposes it is good enough to start with.

I also highly recommend reading KEVM https://core.ac.uk/download/pdf/158321354.pdf , it has a good explanation of EVM machine, execution, and global states. The github for KEVM is here https://github.com/runtimeverification/evm-semantics 

This video on Project Everest gives context for the Vale tool https://www.microsoft.com/en-us/research/video/evercrypt-new-features-and-deployments-with-election-guard-jrc-workshop-2021/ . This video Vale helps get a perspective on the tool itself https://www.youtube.com/watch?v=B4-bnqZ7C2Y&t=2s and slides are here https://www.usenix.org/sites/default/files/conference/protected-files/usenixsecurity17_slides_rane.pdf . Vale documentation https://project-everest.github.io/vale/ is also important to read through.
