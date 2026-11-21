#!/bin/bash
# Like stat-wrapper.sh, but every counter is 0: regress.sh must fail the coverage assertion.
STAT_ZERO=1 exec "$(dirname "$0")/stat-wrapper.sh" "$@"
