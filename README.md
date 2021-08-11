# Verifying Non-Interference Properties For Software Patches
This repo contains the ongoing work to produce non-interference proofs for software patches.

The repo contains operational semantics for LLVM defined in Dafny. Additionally, there is defined instruction level state transitions for a subset of LLVM instructions. Lastly there is a collection of examples of how to represent an LLVM program in terms of the operational semantics in a state machine format, and proofs of safety for these programs.

 > **Note:** Non-Interference proofs coming soon.


This README outlines the steps necessaty for building and verifying dafny files using scons. [See the NuBuild Directory for instructions on building and using the NuBuild tool (This still works but is DEPRECATED - see [here](./NuBuild/README.md) for more info)]


# Setup

To use this project, you will need the following dependencies:

 1. .NET 5.0 SDK (available at `https://dotnet.microsoft.com/download`)
 2. Dafny v3.0.0 (verifier, available at `https://github.com/dafny-lang/dafny`)
 3. python 2 or 3 (needed for running scons)
 4. scons (installable by running `pip install scons`)

# Verifying Files

 1. Use `scons --dafny-path=/path/to/directory/with/dafny/`
 
 The default verification will verify all `.dfy` files in `src/Dafny/examples` (except for `demoChallengeProb1Vuln.i.dfy` because this is an example that shows how vulnerable code would not verify)

 > **Note:** The first time running this, it will take some time as it will verify all `.dfy` files in `src/Dafny/examples` and all of their dependencies. The verification result is cached in a corresponding `.vdfy` file and upon running `scons` again if a specific dependency has not been modified, the cached verification results will be reused at runtime. 


 * To specify a `.dfy` file that you wish to verify use the following command line argument with scons `--verify-root=/path/to/dfy/file` [Note: this will also verify all dependencies of the specified file]
			
* Change the default timeout used during verification with: `--time-limit=[time in seconds]` 

* Turn off trace with: `--no-trace=1` 

To remove all cached verification results use: `./scripts/cleanCachedResults.sh`

 > **Note:** To verify files without the help of the scons tool use: `dotnet /path/to/directory/with/dafny/ [dafny parameters ie. /compile:0 /timeLimit:60 /trace /arith:5 noCheating:1] /path/to/dafnyFile`

## Automation

> **Note:** This is WIP and does not do much at the moment. In the future this will hopefully automatically parse an llvm program into dafny using the operational semantics defined in this repo. This tool also aims to help generate small-step proof lemmas to aid in the production of larger non-interference proofs

Building the automation tool `dotnet build Source/NIP_LLVM.sln`

Running the automation tool `dotnet Binaries/net5.0/NIPLLVM.dll`

## Notes

`Dafny/examples/demoChallengeProblem1.i.dfy` is a good example to look at

## Questions and Issues

If there are any questions or issues with this repo please contact:

Eli Goldweber -- edgoldwe@umich.edu
