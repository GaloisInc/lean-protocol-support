cd ../
git clone https://github.com/leanprover/lean || true
cd lean/
git checkout 667e1e1
mkdir -p build
cd build
cmake -DCMAKE_CXX_COMPILER=g++-6 ../src
make -j 2
