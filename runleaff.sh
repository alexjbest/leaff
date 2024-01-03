
#!/usr/bin/env bash

set -eo pipefail

# this script is used to run Leaff on a pair of directories

# usage: runleaff.sh module olddir newdir

# module is the module to run Leaff on
# olddir and newdir are the directories to run Leaff on
# olddir is the directory with the old project
# newdir is the directory with the new project

# example: runleaff.sh Mathlib ../test-mathlib/ ../test-mathlib2/

if [ $# -ne 3 ]; then
	echo "usage: runleaff.sh module olddir newdir"
	exit 1
fi

lake exe leaff $1 $(tr ':' ',' <<<"$(eval $(lake --dir $2 env) && echo $LEAN_PATH)") $(tr ':' ',' <<<"$(eval $(lake --dir $3 env) && echo $LEAN_PATH)")