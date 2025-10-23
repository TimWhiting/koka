rm -r .koka && mkdir .koka
stack run koka -- --ccopts=-static --cclinkopts=-static --ccopts=-pg --cclinkopts=-pg -o main golang

./main
gprof -E mcount -e __mcount -e __emutls_get_address -e _libc_pthread_getspecific -e pthread_self main gmon* | gprof2dot | dot -Tpng >gprof.png

sudo perf record -F 100 -g ./main
sudo perf script -i perf.data | ~/FlameGraph/stackcollapse-perf.pl | ~/FlameGraph/flamegraph.pl > flamegraph.svg