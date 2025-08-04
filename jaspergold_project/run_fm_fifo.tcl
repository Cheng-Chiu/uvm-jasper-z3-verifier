clear -all
puts "=== Verifying FIFO Buffer ==="

analyze -sv09 \
        ../rtl/fifo.sv \
        fifo_verifier.sv

elaborate -top fifo_verifier -disable_auto_bbox -sv09_expression_mode \
          -parameter DEPTH 8 

clock clock
reset reset

prove -all -bg

report -all

# optional: clean between runs if needed
# reset -all
