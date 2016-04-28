LLVM_SRC_PATH="$HOME/llvm-3.6.2/llvm"
LLVM_BUILD_PATH="$HOME/llvm-3.6.2/build"
LLVM_BIN_PATH="$HOME/llvm-3.6.2/build/bin"
z3_src_path="/home/lb/z3-master"
z3_build_path="/home/lb/z3-master/build"


clang++ -fno-rtti -O0 -g `$LLVM_BIN_PATH/llvm-config --cxxflags` -I$LLVM_SRC_PATH/tools/clang/include -I$LLVM_BUILD_PATH/tools/clang/include main.cpp -I $z3_src_path/src/api -I $z3_src_path/src/api/c++ \
	-Wl,--start-group -lclangAST -lclangAnalysis -lclangBasic -lclangDriver -lclangEdit -lclangFrontend -lclangFrontendTool -lclangLex -lclangParse -lclangSema -lclangEdit -lclangASTMatchers -lclangRewrite -lclangRewriteFrontend -lclangStaticAnalyzerFrontend -lclangStaticAnalyzerCheckers -lclangStaticAnalyzerCore -lclangSerialization -lclangToolingCore -lclangTooling -Wl,--end-group `$LLVM_BIN_PATH/llvm-config --ldflags --libs --system-libs`  -o arrayAnalysis $z3_build_path/libz3.so -lpthread  -lrt





