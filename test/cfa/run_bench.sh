mkdir -p build
pushd build 
cmake .. -DCMAKE_BUILD_TYPE=Release
cmake --build .
popd
stack run koka -- -e bench.kk