#!/bin/zsh
# Run the jobs in jobs.txt one at a time, each only once the machine is quiet (CPU idle at least MINIDLE percent,
# sampled over 2 seconds; macOS load averages also count threads waiting on I/O, so they overstate CPU use),
# recording the idle percentage at the start and end of each job in progress.txt. Jobs already in progress.txt are skipped,
# so the run can be restarted. Start it detached so it outlives the terminal:
#   nohup ./run-sequential.sh > run.log 2>&1 &
S=${0:A:h}
MINIDLE=${MINIDLE:-80}
idle() { top -l 2 -n 0 -s 2 | grep "CPU usage" | tail -1 | sed -E 's/.* ([0-9.]+)% idle.*/\1/' }
touch $S/progress.txt
while read -r line; do
  set -- ${=line}
  if grep -qF "$1 $3 $4 ($5,$6) exit=" $S/progress.txt; then continue; fi
  waited=0
  while (( $(idle) < MINIDLE )); do sleep 15; waited=$((waited + 15)); done
  i0=$(idle)
  $S/job.sh ${=line}
  echo "    idle% start=$i0 end=$(idle) waited=${waited}s" >> $S/progress.txt
done < $S/jobs.txt
echo "ALL DONE $(date)" >> $S/progress.txt
