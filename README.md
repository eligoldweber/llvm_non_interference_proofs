# llvm_model
Dafny model of llvm semantics

# NuBuild tool  -- Mac/Linux
This guide will walk through building and verifying dafny files using the NuBuild tool on Mac or Linux Machines.
You will need to make sure that Dafny and z3 are already downloaded, and will install Bazel by following these  instructions. 


# Setup

To use this project, you will need the following:

 1. .NET 5.0 SDK (available at `https://dotnet.microsoft.com/download`)
 2. Dafny v3.0.0 (verifier, available at `https://github.com/dafny-lang/dafny`)
 3. python 2 or 3 (needed for running scons)
 4. scons (installable by running `pip install scons`)

# Verifying Files

 1. Use `scons --dafny-path=/path/to/directory/with/dafny/`
 
 The default verification will verify all `.dfy` files in `src/Dafny/examples`

 * To specify a `.dfy` file that you wish to verify use the following command line argument with scons `--verify-root=/path/to/dfy/file` [Note: this will also verify all dependencies of the specified file]
			
You can also change the default timeout used during verification with `--time-limit=[time in seconds]` 



## Automation

> **Note:** This is WIP and does not do much at the moment

Building the automation tool `dotnet build Source/NIP_LLVM.sln`

Running the automation tool `dotnet Binaries/net5.0/NIPLLVM.dll`
