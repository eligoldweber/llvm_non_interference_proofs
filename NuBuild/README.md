# [Deprecated tool for building and verifying]



# NuBuild tool  -- Mac/Linux
This guide will walk through building and verifying dafny files using the NuBuild tool on Mac or Linux Machines.
You will need to make sure that Dafny and z3 are already downloaded, and will install Bazel by following these  instructions. 


# Setup

 1. Install Bazel and follow instructions here: (https://docs.bazel.build/versions/master/install.html)
 2. Open and edit ````tools/Dafny/dafny````
 3. Set the ````DAFNY```` variable to the path where the Dafny executable is installed locally on your computer. 
	  (ie ````DAFNY="Home/BASE-DIRECTORY/dafny/Binaries/Dafny.exe"````)

# Building the NuBuild tool

 1. Navigate to the Ironclad/ironfleet directory
 2. Run the following script : ````./buildBazel.sh```` 
 	- This will create a directory in ./tools/NuBuild called bazel-bin
	- There will be two executables in ./tools/NuBuild/bazel-bin/NuBuild; Nubuild.bash and Nubuild.exe

(Optional) -- Building NuBuild tool manually

 1. Navigate to ````tools/NuBuild````
 2. Run ````bazel build --spawn_strategy=standalone //NuBuild:NuBuild````

# Verifying Files

 1. Navigate to the root directory
 2. To execute the NuBuild Executable run: ````./tools/NuBuild/bazel-bin/NuBuild/NuBuild.bash````
	- This command is equivalent to ````./bin_tools/NuBuild/NuBuild.exe```` in (https://github.com/microsoft/Ironclad/tree/master/ironfleet#verification)
			
To verify an individual Dafny file (and all of its dependencies), run:
````./tools/NuBuild/bazel-bin/NuBuild/NuBuild.bash --no-cloudcache -j 3 DafnyVerifyTree src/Dafny/llvm.i.dfy````
			 

> **Note:** Always use --no-cloudcache. This version of NuBuild does not support clusters of cloud VMs to parallelize verification

## Possible Errors/Issues

 - non-CRLF line endings in source file ... 
	 - 
	 - try using ````unix2dos```` command

## [IMPORTANT] DAFNY VERSION
Due to "https://github.com/dafny-lang/dafny/issues/301" Inorder to run fully and succesfully follow the advice from this post and make sure to build Dafny manually from the e9f5c05d59919eb7a23e10ad47318a8692843551 commit 

## [IMPORTANT] z3 VERSION
Use z3 Version 4.6.0 -- [https://github.com/Z3Prover/z3/releases/tag/z3-4.6.0]

