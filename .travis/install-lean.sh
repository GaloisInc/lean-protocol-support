cd ../
git clone https://github.com/leanprover/lean || true
cd lean/
git checkout fa9c868ed2bba1b6e38c49c03a75e86c6cbda0ac
mkdir -p build
cd build
cmake -DCMAKE_CXX_COMPILER=g++-6 ../src
make -j 2
