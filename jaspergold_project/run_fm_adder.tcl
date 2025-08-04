clear -all
puts "=== Verifying Carry Select Adder ==="

analyze -sv09 \
        ../rtl/carry_select_adder.sv \
        adder_verifier.sv

elaborate -top adder_verifier -disable_auto_bbox -sv09_expression_mode

clock clock
reset reset

prove -all -bg

report -all

# optional: clean between runs if needed
# reset -all
