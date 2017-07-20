git clone https://github.com/leanprover/lean
cd lean/
git checkout ae5bc52
mkdir build
cd build
cmake ../src -G Ninja
ninja
cd ../
