# InvariantSynthesisForArray_C

We offer a binares file, which can be executed in ubuntu 64bit(&gt;= 14.04). 

<b>Execute:</b>

<span style="background: #dddddd"><span style="font-weight: normal">./arrayAnalysis_x64 ../testcase/array.cpp --</span></span>


If it can not be executed in your linux system. you can build it.

<b>Building InvariantSynthesisForArray_C using Z3 and Clang</b>

1. you must build Z3  in your system. please see it in https://github.com/Z3Prover/z3

2. you must build clang(&gt;=3.6.2) in your system. please see it in http://clang.llvm.org/get_started.html. 

3. cd src, edit compile.sh, set LLVM_SRC_PATH, LLVM_BUILD_PATH, LLVM_BIN_PATH, z3_src_path and z3_build_path, then run compile.sh

