IConFuzz
========

IConFuzz is a grey-box fuzzer for Ethereum smart contracts.

# Installation

IConFuzz is written in F#, so you have to install .NET to run IConFuzz.
Installation step differs for each Linux distribution, so please refer to this
[link](https://docs.microsoft.com/en-us/dotnet/core/install/) and install
net8.0. Then, you can simply clone and build IConFuzz as follow.

```
$ git clone https://github.com/infosec-sogang/IConFuzz
$ cd IConFuzz
$ git submodule update --init --recursive
$ make
```

# Usage

You can fuzz a smart contract with IConFuzz by providing its EVM bytecode and
ABI specification as follow. Here, `-t` option specifies the time limitation in
seconds. The output test cases and bug-triggering inputs will be stored in the
directory specified by `-o` option.

```
$ dotnet build/IConFuzz.dll fuzz -p <source file> -m <main contract name> -t <time limit> -o <output dir>
```

The output directory will have two subdirectories. First, `testcase` directory
will contain inputs that increased edge coverage during fuzzing. You can use
these inputs to measure code coverage achievement. Second, `bug` directory will
contain inputs that triggered bug. The file names of bug-triggering inputs will
be tagged with abbreviated bug class name (e.g., 'EL' for ether leak bug).

Note that the generated test inputs are in JSON format, and they contain
necessary information required to reproduce the transactions. You can replay
these files against the target contract with the following command.

```
$ dotnet build/IConFuzz.dll replay -p <source file> -i <test case directory>
```

You may also check other command-line options of IConFuzz by running `dotnet
build/IConFuzz.dll fuzz --help` and `dotnet build/IConFuzz.dll replay --help`.

# Artifact

We also publicize the artifacts to reproduce the experiments in our paper.
Please check our
[IConFuzz-Artifact](https://github.com/infosec-sogang/IConFuzz-Artifact)
repository.
