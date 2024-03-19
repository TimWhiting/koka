if ! [ -d "alex" ]; then
  git clone https://github.com/TimWhiting/alex
fi
cd alex
# cd alex && git checkout koka_output && git fetch --all
# git reset --hard origin/koka_output
stack build
stack run alex -- -k ../lib/std/data/json-alex.x -o ../lib/std/data/json-parse.kk