#!/bin/bash
# Like stat-wrapper.sh, but hangs on about 30% of the instances (chosen by a
# checksum of the file, the last argument), so that a stress row sees
# solver timeouts: used by tests/test_regress_limits.sh.
if [ $(( $(cksum < "${@: -1}" | cut -d' ' -f1) % 10 )) -lt 3 ]; then
    exec sleep 1000
fi
exec "$(dirname "$0")/stat-wrapper.sh" "$@"
