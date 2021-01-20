# See LICENSE for license details.

# Read the specified list of IP files
read_ip [glob -directory $ipdir [file join * {*.xci}]]

# Replace MIG IP with modified one
exec rm -r obj/ip/vc707mig4gb/vc707mig4gb/user_design/rtl
exec cp -r ../../migrtl obj/ip/vc707mig4gb/vc707mig4gb/user_design/rtl

# Synthesize the design
synth_design -top $top -flatten_hierarchy rebuilt

# Checkpoint the current design
write_checkpoint -force [file join $wrkdir post_synth]
