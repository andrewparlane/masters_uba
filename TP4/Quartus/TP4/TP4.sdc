create_clock -period 50MHz -name CLOCK_50 CLOCK_50

create_generated_clock -source {pll_inst|altpll_component|pll|inclk[0]} -multiply_by 2 -duty_cycle 50.00 -name clk100M {pll_inst|altpll_component|pll|clk[0]}
create_generated_clock -source {pll_inst|altpll_component|pll|inclk[0]} -divide_by 2 -duty_cycle 50.00 -name clk25M {pll_inst|altpll_component|pll|clk[1]}

derive_clock_uncertainty
