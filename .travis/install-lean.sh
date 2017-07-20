git clone https://github.com/leanprover/lean
git checkout ae5bc52
cd lean/
mkdir build
cd build
cmake ../src -G Ninja
ninja
cd ../
