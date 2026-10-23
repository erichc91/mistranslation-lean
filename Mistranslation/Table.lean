import Mistranslation.LindemannBridge
import Mistranslation.BratuOde
import Mistranslation.Breaks
import Mistranslation.Csch2Pair
import Mistranslation.EckartPair
import Mistranslation.HotWire
import Mistranslation.HypGen
import Mistranslation.HypOde
import Mistranslation.KThreeCalc
import Mistranslation.KThreeClass
import Mistranslation.KeplerClass
import Mistranslation.KeplerOde
import Mistranslation.LinearOde
import Mistranslation.MemsOde
import Mistranslation.MorseBreak
import Mistranslation.MorseClass
import Mistranslation.MorseOde
import Mistranslation.PFiveClass
import Mistranslation.PThreeClass
import Mistranslation.PairLaw
import Mistranslation.PinneyInv
import Mistranslation.PinneySpring
import Mistranslation.RankLaw
import Mistranslation.Recipe
import Mistranslation.StraightenLaw
import Mistranslation.TrigClass
import Mistranslation.TrigPredicted
import Mistranslation.TrioSeat
import Mistranslation.TippingRule
import Mistranslation.SpringFamily
import Mistranslation.KThreeOde
import Mistranslation.TrigPredictedOde
import Mistranslation.PThreeOde
import Mistranslation.PFiveOde
import Mistranslation.PThreeBreak
import Mistranslation.PFiveBreak
import Mistranslation.TimeMap
import Mistranslation.PurePower
import Mistranslation.TimeMapExists
import Mistranslation.WeakeningFlip
import Mistranslation.CircleEckart
import Mistranslation.InfinitelyMany
import Mistranslation.Pinch
import Mistranslation.PinchBreak
import Mistranslation.PinchMax
import Mistranslation.ShiftedSpring
import Mistranslation.ShiftedSpringNeg

/-! # The break table, built together (2026-10-23, Classified Table phase C6)

Every closure file in one build. The rank-1 results that used to take Hermite-Lindemann or Lindemann-for-sine as an
argument are restated here with that argument filled by the proved theorems in `LindemannBridge`, so each statement
below carries no outside hypothesis. `#print axioms` at the bottom is the sweep. -/

namespace BreakTable

open LindemannBridge

theorem bratu_end_to_end : type_of% (@BratuOde.bratu_break_end_to_end hermite_lindemann) := @BratuOde.bratu_break_end_to_end hermite_lindemann
theorem mems_break : type_of% (@Breaks.mems_break_transcendental hermite_lindemann) := @Breaks.mems_break_transcendental hermite_lindemann
theorem bratu_break : type_of% (@Breaks.bratu_break_transcendental hermite_lindemann) := @Breaks.bratu_break_transcendental hermite_lindemann
theorem break_of_link : type_of% (@Breaks.break_transcendental_of_link hermite_lindemann) := @Breaks.break_transcendental_of_link hermite_lindemann
theorem k32_break : type_of% (@Breaks.k32_break_transcendental hermite_lindemann) := @Breaks.k32_break_transcendental hermite_lindemann
theorem k43_break : type_of% (@Breaks.k43_break_transcendental hermite_lindemann) := @Breaks.k43_break_transcendental hermite_lindemann
theorem ladderA_break : type_of% (@Breaks.ladderA_break_transcendental hermite_lindemann) := @Breaks.ladderA_break_transcendental hermite_lindemann
theorem predicted_hyp_end_to_end : type_of% (@HypGen.break_end_to_end hermite_lindemann) := @HypGen.break_end_to_end hermite_lindemann
theorem hyp_end_to_end : type_of% (@HypOde.hyp_break_end_to_end hermite_lindemann) := @HypOde.hyp_break_end_to_end hermite_lindemann
theorem kepler_class : type_of% (@KeplerOde.class_of_crit hermite_lindemann) := @KeplerOde.class_of_crit hermite_lindemann
theorem kepler_break : type_of% (@KeplerOde.break_transcendental hermite_lindemann) := @KeplerOde.break_transcendental hermite_lindemann
theorem k3_top : type_of% (@KThree.top_transcendental hermite_lindemann) := @KThree.top_transcendental hermite_lindemann
theorem k3_class : type_of% (@KThree.class_of_crit hermite_lindemann) := @KThree.class_of_crit hermite_lindemann
theorem mems_end_to_end : type_of% (@MemsOde.mems_break_end_to_end hermite_lindemann) := @MemsOde.mems_break_end_to_end hermite_lindemann
theorem morse_class : type_of% (@MorseOde.class_of_crit hermite_lindemann) := @MorseOde.class_of_crit hermite_lindemann
theorem morse_break : type_of% (@MorseOde.break_transcendental hermite_lindemann) := @MorseOde.break_transcendental hermite_lindemann
theorem p5_class : type_of% (@PFive.class_of_crit hermite_lindemann) := @PFive.class_of_crit hermite_lindemann
theorem pinney_inv_break : type_of% (@PinneyInv.break_transcendental hermite_lindemann) := @PinneyInv.break_transcendental hermite_lindemann
theorem pinney_spring_seat : type_of% (@PinneySpring.table_seat lindemann_sin) := @PinneySpring.table_seat lindemann_sin
theorem p3_class : type_of% (@PThree.class_of_crit hermite_lindemann) := @PThree.class_of_crit hermite_lindemann
theorem p3_circle_class : type_of% (@PThree.class_of_crit_circle lindemann_sin) := @PThree.class_of_crit_circle lindemann_sin
theorem recipe : type_of% (@Recipe.transcendental_of_recipe hermite_lindemann) := @Recipe.transcendental_of_recipe hermite_lindemann
theorem recipe' : type_of% (@Recipe.transcendental_of_recipe' hermite_lindemann) := @Recipe.transcendental_of_recipe' hermite_lindemann
theorem pi_transcendental : type_of% (@TrigClass.pi_transcendental lindemann_sin) := @TrigClass.pi_transcendental lindemann_sin
theorem linear_break : type_of% (@TrigClass.linear_break_transcendental lindemann_sin) := @TrigClass.linear_break_transcendental lindemann_sin
theorem pinney_spring : type_of% (@TrigClass.pinney_spring_transcendental lindemann_sin) := @TrigClass.pinney_spring_transcendental lindemann_sin
theorem trig_predicted : type_of% (@TrigPredicted.break_transcendental lindemann_sin) := @TrigPredicted.break_transcendental lindemann_sin


-- axiom sweep: every line must read [propext, Classical.choice, Quot.sound] (or a subset)
#print axioms bratu_end_to_end
#print axioms mems_break
#print axioms bratu_break
#print axioms break_of_link
#print axioms k32_break
#print axioms k43_break
#print axioms ladderA_break
#print axioms predicted_hyp_end_to_end
#print axioms hyp_end_to_end
#print axioms kepler_class
#print axioms kepler_break
#print axioms k3_top
#print axioms k3_class
#print axioms mems_end_to_end
#print axioms morse_class
#print axioms morse_break
#print axioms p5_class
#print axioms pinney_inv_break
#print axioms pinney_spring_seat
#print axioms p3_class
#print axioms p3_circle_class
#print axioms recipe
#print axioms recipe'
#print axioms pi_transcendental
#print axioms linear_break
#print axioms pinney_spring
#print axioms trig_predicted

-- C3: unconditional reductions (no Schanuel hypothesis anywhere; the open fact is recorded as data in seat_ledger)
#print axioms PairLaw.pair_reduction
#print axioms PairLaw.trio_reduction
#print axioms RankLaw.rank_reduction
#print axioms Csch2Pair.break_reduction
#print axioms EckartPair.break_reduction
#print axioms TrioSeat.break_reduction

-- C2 tipping rule + spring families
#print axioms TippingRule.homogeneous_no_break
#print axioms TippingRule.steady_no_break
#print axioms TippingRule.exp_spring_no_break
#print axioms TippingRule.wrong_sign_power_only_zero
#print axioms TippingRule.weakening_le_one
#print axioms SpringFamily.forced_break_transcendental
#print axioms SpringFamily.free_first_wobble_transcendental
#print axioms SpringFamily.restoring_first_wobble

-- C1 ODE links (end to end: K_3 bridge, circle twin; P_3 / P_5 time-condition links)
#print axioms KThreeOde.break_end_to_end
#print axioms TrigPredictedOde.break_end_to_end
#print axioms PThreeOde.time_condition_crit_vars
#print axioms PFiveOde.time_condition_crit_vars

-- P_3 end to end; sign-blind linear seats
#print axioms PThreeBreak.break_end_to_end
#print axioms ShiftedSpring.wobble_set_class
#print axioms ShiftedSpring.forced_break_transcendental
#print axioms ShiftedSpring.forced_no_break
#print axioms ShiftedSpring.forced_neg_empty
#print axioms ShiftedSpring.forced_neg_class
#print axioms ShiftedSpringNeg.forced_neg_no_break

-- P_5 end to end; time map (every polynomial seat)
#print axioms PFiveBreak.break_end_to_end
#print axioms TimeMap.poly_push_eq_time_map
#print axioms TimeMap.tip_reduction_break

-- pure-power peak reduction
#print axioms PurePower.peak_reduction

-- time-map existence; weakening seats (both orientations)
#print axioms TimeMapExists.time_map_exists
#print axioms TimeMapExists.Weakening.weakening_no_break
#print axioms WeakeningFlip.flipped_no_break

-- circle Eckart: local time map + tip reduction
#print axioms CircleEckart.push_eq_time_map_local
#print axioms CircleEckart.Circle.circle_tip_reduction

-- the law makes infinitely many transcendental breaks
#print axioms InfinitelyMany.certified_infinite

-- the pinch: closed forms and the critical-value transcendence (derivative link pending)
#print axioms Pinch.T_sq_closed
#print axioms Pinch.crit_transcendental

-- the pinch: dT/dA = 0 at a pinch point => transcendental; lam* exists (global-max link pending)
#print axioms PinchBreak.fold_transcendental
#print axioms PinchBreak.lam_star_exists

-- the pinch, end to end: the break of the lam* seat is the greatest push and is transcendental
#print axioms PinchMax.break_lam_star

end BreakTable
