#!/bin/sh

# This contains build commands for all the mm1 files that are actually complete
# It assumes that 'mm0-rs' and 'mm0-c' are available on the PATH

mm0-rs compile peano.mm1 peano.mmb
mm0-c peano.mmb < peano.mm0

mm0-rs join peano_hex.mm0 > peano_hex_join.mm0
mm0-rs compile peano_hex.mm1 peano_hex.mmb
mm0-c peano_hex.mmb < peano_hex_join.mm0

# mm0-rs join mm0.mm0 > mm0_join.mm0
# mm0-rs compile mm0.mm1 mm0.mmb
# mm0-c mm0.mmb < mm0_join.mm0

# mm0-rs join x86.mm0 > x86_join.mm0
# mm0-rs compile x86.mm1 x86.mmb
# mm0-c x86.mmb < x86_join.mm0