cd ../
git clone https://github.com/leanprover/lean || true
cd lean/
git checkout 32ddac5f40a7abd4bf040d7f631e4a859e45868a
mkdir -p build
cd build
cmake -DCMAKE_CXX_COMPILER=g++-6 ../src
make -j 2
