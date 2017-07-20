git clone https://github.com/leanprover/lean
cd lean/
git checkout ae5bc52
mkdir build
cd build
cmake -DCMAKE_CXX_COMPILER=g++-6 ../src
make -j 2
