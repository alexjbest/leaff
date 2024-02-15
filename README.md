Leaff
=====

Leaff is a diff tool for Lean environments. It aims to produce a human readable summary of the differences between two versions of the same Lean module (for instance coming from olean files from two different revisions to the same library). For example it can be used to detect unexpected changes to, or removal of, theorems when a refactor is carried out in a large library. Or it can be useful to simply summarize the diff of a proposed inclusion with the more likely to be interesting information presented first.

It is currently under development and should be considered version alpha (contributions welcome!).
Nevertheless at the moment it does at least provide some potentially useful output
and it is at least fast enough to run on the scale of `mathlib`.

Usage
-----

The main entrypoint is the script `runleaff.sh` to use it you should check out two copies of your project, one for the old version of the library and one for the new (e.g. with `git worktree add ../old/ some-other-branch`), 
build both by running `lake build` in the corresponding directories, then navigate to the Leaff directory and run
```
./runleaff.sh ModuleName /path/to/old-version/ /path/to/new-version/
```
note that the module name will likely just be the name of the library (e.g. `Mathlib`) if want to know all potential downstream changes of some change, but could be more specific, e.g. `MyLibrary.SomeFile`. The paths could be relative to the Leaff directory or absolute.

You may face many issues, especially if the diff is too big, if there are different Lean versions use in the libraries, or if there is a different Lean version used to compile the libraries and Leaff itself.

```diff
$ ./runleaff.sh Mathlib ../test-mathlib2/ ../test-mathlib/
Found differences:
@@ Mathlib.Algebra.GroupPower.Order @@
+ added le_of_pow_le_pow_left.{u_2}
+ added pow_le_pow_iff_left.{u_2}
+ added pow_right_injective.{u_2}
@@ Mathlib.Data.Nat.Pow @@
+ added Nat.pow_lt_pow_left
+ added Nat.pow_le_pow_right
+ added Nat.pow_lt_pow_iff_left
@@ Mathlib.Algebra.GroupPower.Order @@
+ added pow_lt_pow_iff_left.{u_2}
+ added pow_lt_pow_right_of_lt_one.{u_2}
+ added pow_right_inj.{u_2}
+ added pow_lt_pow_left.{u_2}
@@ Mathlib.Data.Nat.Pow @@
+ added Nat.pow_le_pow_iff_left
+ added Nat.pow_le_pow_left
@@ Mathlib.Algebra.GroupPower.Order @@
+ added pow_left_strictMonoOn.{u_2}
+ added pow_lt_pow_right.{u_2}
@@ Mathlib.Data.Nat.Pow @@
- removed Nat.pow_lt_pow_of_lt_left
@@ Mathlib.Algebra.GroupPower.Order @@
- removed pow_lt_pow
@@ Mathlib.Data.Nat.Pow @@
- removed Nat.pow_le_iff_le_right
- removed Nat.pow_le_iff_le_left
- removed Nat.pow_right_strictMono
@@ Mathlib.Algebra.GroupPower.Order @@
- removed pow_lt_pow_of_lt_left
- removed self_le_pow
@@ Mathlib.Data.Nat.Pow @@
- removed Nat.pow_lt_pow_of_lt_right
@@ Mathlib.Combinatorics.Additive.Behrend @@
- removed Behrend.two_le_nValue
@@ Mathlib.Data.Nat.Pow @@
- removed Nat.pow_lt_iff_lt_right
- removed Nat.pow_lt_iff_lt_left
@@ Mathlib.Algebra.GroupPower.Order @@
- removed strictMonoOn_pow
- removed le_of_pow_le_pow
- removed pow_lt_pow_of_lt_one
@@ Mathlib.NumberTheory.LucasLehmer @@
! type changed for LucasLehmer.sMod_lt
@@ Mathlib.Algebra.GroupPower.Order @@
! type changed for pow_left_inj
! type changed for one_le_pow_iff_of_nonneg
@@ Mathlib.Data.Nat.Pow @@
! type changed for StrictMono.nat_pow
! type changed for Nat.one_lt_two_pow
@@ Mathlib.Algebra.GroupPower.Order @@
! type changed for pow_lt_one_iff_of_nonneg
! type changed for pow_eq_one_iff_of_nonneg
@@ Mathlib.Data.Nat.Pow @@
! type changed for Nat.pow_left_strictMono
@@ Mathlib.Algebra.GroupPower.Order @@
! type changed for pow_le_one_iff_of_nonneg
@@ Mathlib.NumberTheory.Divisors @@
! type changed for Nat.properDivisors_prime_pow
@@ Mathlib.NumberTheory.LucasLehmer @@
! type changed for LucasLehmer.mersenne_int_pos
@@ Mathlib.Algebra.GroupPower.Order @@
! type changed for one_lt_pow_iff_of_nonneg
@@ Mathlib.Combinatorics.Additive.Behrend @@
! type changed for Behrend.bound
@@ Mathlib.NumberTheory.Multiplicity @@
! type changed for padicValNat.pow_sub_pow
@@ Mathlib.NumberTheory.LucasLehmer @@
! type changed for LucasLehmer.mersenne_int_ne_zero
@@ Mathlib.Data.Nat.Pow @@
! type changed for Nat.one_lt_pow
@@ Mathlib.Algebra.GroupPower.Order @@
! type changed for abs_pow_eq_one
@@ Mathlib.NumberTheory.Multiplicity @@
! type changed for padicValNat.pow_two_sub_pow
@@ Mathlib.Data.Nat.Pow @@
! type changed for Nat.pow_left_injective
! type changed for Nat.one_lt_pow_iff
@@ Mathlib.NumberTheory.LucasLehmer @@
! type changed for LucasLehmer.sMod_nonneg
@@ Mathlib.Data.Nat.Pow @@
+ attribute protected added to Nat.pow_le_pow_iff_left
+ attribute protected added to Nat.pow_right_injective
+ attribute protected added to Nat.pow_le_pow_left
+ attribute protected added to Nat.pow_lt_pow_left
+ attribute protected added to Nat.pow_left_strictMono
+ attribute protected added to Nat.pow_le_pow_right
+ attribute protected added to Nat.pow_lt_pow_iff_left
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed le_of_nsmul_le_nsmul → le_of_nsmul_le_nsmul_right'
! renamed pow_lt_pow_iff' → pow_lt_pow_iff_right'
! renamed le_of_pow_le_pow' → le_of_pow_le_pow_left'
! renamed nsmul_strictMono_right → nsmul_left_strictMono
! renamed nsmul_le_nsmul → nsmul_le_nsmul_left
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed pow_lt_pow_iff_of_lt_one → pow_lt_pow_iff_right_of_lt_one
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed pow_strictMono_left → pow_right_strictMono'
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed pow_lt_pow_iff → pow_lt_pow_iff_right
! renamed pow_le_pow_iff → pow_le_pow_iff_right
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed pow_le_pow_of_le_one' → pow_le_pow_right_of_le_one'
! renamed pow_strictMono_right' → pow_left_strictMono
! renamed StrictMono.nsmul_left → StrictMono.const_nsmul
! renamed Monotone.nsmul_left → Monotone.const_nsmul
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed pow_le_pow → pow_le_pow_right
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed nsmul_le_nsmul_of_nonpos → nsmul_le_nsmul_left_of_nonpos
! renamed pow_le_pow' → pow_le_pow_right'
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed pow_le_pow_of_le_left → pow_le_pow_left
! renamed lt_of_pow_lt_pow → lt_of_pow_lt_pow_left
! renamed self_lt_pow → lt_self_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed pow_le_pow_of_le_left' → pow_le_pow_left'
@@ Mathlib.RingTheory.Ideal.Operations @@
! renamed Ideal.pow_le_pow → Ideal.pow_le_pow_right
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed lt_of_nsmul_lt_nsmul → lt_of_nsmul_lt_nsmul_right
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed pow_mono → pow_right_mono
! renamed pow_lt_pow₀ → pow_lt_pow_right₀
! renamed pow_strictMono_right → pow_right_strictMono
@@ Mathlib.Data.Real.ENNReal @@
! renamed ENNReal.pow_lt_pow_of_lt_left → ENNReal.pow_lt_pow_left
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed nsmul_lt_nsmul → nsmul_lt_nsmul_left
! renamed pow_lt_pow' → pow_lt_pow_right'
@@ Mathlib.Algebra.GroupPower.Order @@
! renamed strictAnti_pow → pow_right_strictAnti
@@ Mathlib.RingTheory.DedekindDomain.Ideal @@
! renamed Ideal.strictAnti_pow → Ideal.pow_right_strictAnti
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed lt_of_pow_lt_pow' → lt_of_pow_lt_pow_left'
@@ Mathlib.RingTheory.Ideal.Operations @@
! renamed Ideal.pow_mono → Ideal.pow_right_mono
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed nsmul_strictMono_left → nsmul_right_strictMono
! renamed nsmul_le_nsmul_iff → nsmul_le_nsmul_iff_left
@@ Mathlib.Algebra.GroupPower.Lemmas @@
! renamed zpow_strictMono_right → zpow_right_strictMono
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! renamed StrictMono.pow_right' → StrictMono.pow_const
! renamed nsmul_le_nsmul_of_le_right → nsmul_le_nsmul_right
! renamed pow_le_pow_iff' → pow_le_pow_iff_right'
! renamed nsmul_lt_nsmul_iff → nsmul_lt_nsmul_iff_left
@@ Mathlib.Data.Nat.Pow @@
+ doc added to Nat.pow_le_pow_left
@@ Mathlib.Algebra.GroupPower.Order @@
+ doc added to pow_left_strictMonoOn
+ doc added to pow_right_strictMono
@@ Mathlib.Data.Nat.Pow @@
+ doc added to Nat.pow_left_strictMono
+ doc added to Nat.pow_le_pow_right
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! doc _  ified for pow_left_strictMono
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_eq_one_iff_of_nonneg
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for LucasLehmer.mersenne_int_pos
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for StrictMono.const_nsmul
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_left_injective
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Monotone.const_nsmul
@@ Mathlib.Data.Nat.Pow @@
! proof changed for StrictMono.nat_pow
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_le_pow_right
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for LucasLehmer.sMod_nonneg
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_le_nsmul_left_of_nonpos
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for one_lt_pow_iff_of_nonneg
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_le_pow_right'
! proof changed for nsmul_right_strictMono
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_le_pow_left
@@ Mathlib.Combinatorics.Additive.Behrend @@
! proof changed for Behrend.bound
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for lt_of_pow_lt_pow_left
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for StrictMono.pow_const
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for lt_self_pow
! proof changed for one_le_pow_iff_of_nonneg
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_le_pow_left'
! proof changed for nsmul_le_nsmul_right
! proof changed for le_of_nsmul_le_nsmul_right'
@@ Mathlib.NumberTheory.Multiplicity @@
! proof changed for padicValNat.pow_sub_pow
@@ Mathlib.Data.Nat.Factorization.Basic @@
! proof changed for Nat.factorization_lt
@@ Mathlib.Algebra.Order.Archimedean @@
! proof changed for exists_lt_nsmul
@@ Mathlib.Analysis.InnerProductSpace.Basic @@
! proof changed for eq_of_norm_le_re_inner_eq_norm_sq
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Right.pow_nonpos
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.log_pow
@@ Mathlib.FieldTheory.Finite.Basic @@
! proof changed for FiniteField.X_pow_card_pow_sub_X_natDegree_eq
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Right.pow_le_one_of_le
@@ Mathlib.Data.Nat.Factorial.Basic @@
! proof changed for Nat.pow_sub_lt_descFactorial'
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for MonovaryOn.nsmul_left
@@ Mathlib.Computability.Ackermann @@
! proof changed for ack_three
@@ Mathlib.Analysis.SpecialFunctions.Exp @@
! proof changed for Real.tendsto_exp_div_pow_atTop
@@ Mathlib.Data.Nat.Size @@
! proof changed for Nat.size_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_nonneg
@@ Mathlib.Computability.Ackermann @@
! proof changed for ack_add_one_sq_lt_ack_add_four
@@ Mathlib.GroupTheory.Archimedean @@
! proof changed for AddSubgroup.exists_isLeast_pos
@@ Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree @@
! proof changed for Polynomial.cardPowDegree_anti_archimedean
@@ Mathlib.Data.Nat.Factorization.Basic @@
! proof changed for Nat.factorization_le_of_le_pow
@@ Mathlib.Analysis.InnerProductSpace.Basic @@
! proof changed for InnerProductSpace.toUniformConvexSpace
@@ Mathlib.NumberTheory.NumberField.Discriminant @@
! proof changed for NumberField.discr_gt_one
@@ Mathlib.RingTheory.DiscreteValuationRing.TFAE @@
! proof changed for DiscreteValuationRing.TFAE
@@ Mathlib.NumberTheory.PellMatiyasevic @@
! proof changed for Pell.eq_pow_of_pell
@@ Mathlib.NumberTheory.NumberField.Discriminant @@
! proof changed for NumberField.abs_discr_ge
@@ Mathlib.RingTheory.WittVector.Frobenius @@
! proof changed for WittVector.map_frobeniusPoly.key₂
@@ Mathlib.NumberTheory.ClassNumber.Finite @@
! proof changed for ClassGroup.norm_lt
@@ Mathlib.Analysis.Analytic.Composition @@
! proof changed for FormalMultilinearSeries.comp_summable_nnreal
@@ Mathlib.Analysis.SpecificLimits.FloorPow @@
! proof changed for sum_div_pow_sq_le_div_sq
@@ Mathlib.Algebra.GeomSum @@
! proof changed for nat_sub_dvd_pow_sub_pow
@@ Mathlib.Analysis.Calculus.FDeriv.Measurable @@
! proof changed for RightDerivMeasurableAux.D_subset_differentiable_set
@@ Mathlib.Data.Complex.Exponential @@
! proof changed for Real.cos_two_neg
@@ Mathlib.RingTheory.Polynomial.Basic @@
! proof changed for Polynomial.Monic.geom_sum
@@ Mathlib.Topology.Metrizable.Uniformity @@
! proof changed for UniformSpace.metrizable_uniformity
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for sq_lt_sq
@@ Mathlib.FieldTheory.Finite.Polynomial @@
! proof changed for MvPolynomial.degrees_indicator
@@ Mathlib.Analysis.Asymptotics.Asymptotics @@
! proof changed for Asymptotics.IsBigOWith.of_pow
@@ Mathlib.NumberTheory.Padics.PadicIntegers @@
! proof changed for PadicInt.norm_le_pow_iff_le_valuation
@@ Mathlib.Analysis.Complex.Basic @@
! proof changed for Complex.nnnorm_eq_one_of_pow_eq_one
@@ Mathlib.Analysis.PSeries @@
! proof changed for Finset.sum_condensed_le
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.one_lt_two_pow'
@@ Mathlib.NumberTheory.DirichletCharacter.Bounds @@
! proof changed for DirichletCharacter.unit_norm_eq_one
@@ Mathlib.Analysis.PSeries @@
! proof changed for ENNReal.tsum_condensed_le
@@ Mathlib.RingTheory.DiscreteValuationRing.TFAE @@
! proof changed for exists_maximalIdeal_pow_eq_of_principal
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for AntivaryOn.pow_left
@@ Mathlib.Analysis.SpecificLimits.FloorPow @@
! proof changed for sum_div_nat_floor_pow_sq_le_div_sq
@@ Mathlib.NumberTheory.SumFourSquares @@
! proof changed for Int.lt_of_sum_four_squares_eq_mul
@@ Mathlib.Algebra.GroupPower.Lemmas @@
! proof changed for zpow_le_zpow_iff
@@ Mathlib.NumberTheory.Liouville.LiouvilleWith @@
! proof changed for Liouville.frequently_exists_num
@@ Mathlib.Analysis.SpecialFunctions.Log.Deriv @@
! proof changed for Real.abs_log_sub_add_sum_range_le
@@ Mathlib.RingTheory.DedekindDomain.Ideal @@
! proof changed for Ideal.pow_lt_self
@@ Mathlib.Combinatorics.SetFamily.FourFunctions @@
! proof changed for Finset.card_le_card_diffs
@@ Mathlib.NumberTheory.Liouville.Basic @@
! proof changed for Liouville.transcendental
@@ Mathlib.Analysis.SpecificLimits.Normed @@
! proof changed for summable_geometric_iff_norm_lt_1
@@ Mathlib.Algebra.IsPrimePow @@
! proof changed for isPrimePow_nat_iff_bounded
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Left.one_le_pow_of_le
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_lt_pow_succ
@@ Mathlib.Data.Polynomial.Degree.CardPowDegree @@
! proof changed for Polynomial.cardPowDegree_isEuclidean
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_right_injective
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Left.pow_nonpos
@@ Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology @@
! proof changed for Ideal.adic_module_basis
@@ Mathlib.NumberTheory.PellMatiyasevic @@
! proof changed for Pell.eq_pow_of_pell_lem
@@ Mathlib.Analysis.NormedSpace.FiniteDimension @@
! proof changed for Basis.op_nnnorm_le
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_pos_iff
! proof changed for sq_lt_one_iff
@@ Mathlib.RingTheory.Henselian @@
! proof changed for IsAdicComplete.henselianRing
@@ Mathlib.Analysis.ODE.PicardLindelof @@
! proof changed for PicardLindelof.FunSpace.dist_iterate_next_le
@@ Mathlib.NumberTheory.Divisors @@
! proof changed for Nat.prod_properDivisors_prime_pow
@@ Mathlib.MeasureTheory.Integral.PeakFunction @@
! proof changed for tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
@@ Mathlib.NumberTheory.Bertrand @@
! proof changed for centralBinom_le_of_no_bertrand_prime
@@ Mathlib.Data.Nat.Bitwise @@
! proof changed for Nat.testBit_two_pow_of_ne
@@ Mathlib.NumberTheory.FLT.Four @@
! proof changed for Fermat42.coprime_of_minimal
@@ Mathlib.Analysis.Analytic.Composition @@
! proof changed for HasFPowerSeriesAt.comp
@@ Mathlib.Algebra.Tropical.Basic @@
! proof changed for Tropical.add_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Right.one_le_pow_of_le
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.clog_anti_left
@@ Mathlib.MeasureTheory.Measure.Hausdorff @@
! proof changed for MeasureTheory.hausdorffMeasure_pi_real
@@ Mathlib.Combinatorics.Additive.PluenneckeRuzsa @@
! proof changed for Finset.card_pow_div_pow_le
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Antivary.nsmul_right
@@ Mathlib.Algebra.GroupPower.Lemmas @@
! proof changed for strictMono_pow_bit1
@@ Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar @@
! proof changed for MeasureTheory.Measure.addHaar_submodule
@@ Mathlib.Data.Nat.Factorial.Basic @@
! proof changed for Nat.ascFactorial_lt_pow_add
@@ Mathlib.Topology.Algebra.Polynomial @@
! proof changed for Polynomial.coeff_bdd_of_roots_le
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Antivary.pow_right
@@ Mathlib.Topology.Algebra.InfiniteSum.Order @@
! proof changed for Finite.of_summable_const
@@ Mathlib.Analysis.PSeries @@
! proof changed for sum_Ioo_inv_sq_le
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for le_self_pow
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_dvd_pow_iff_pow_le_pow
@@ Mathlib.RingTheory.Polynomial.Basic @@
! proof changed for Polynomial.coeff_prod_mem_ideal_pow_tsub
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Antivary.pow_left
@@ Mathlib.NumberTheory.NumberField.Units @@
! proof changed for NumberField.Units.dirichletUnitTheorem.seq_next
@@ Mathlib.Computability.Ackermann @@
! proof changed for exists_lt_ack_of_nat_primrec
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for MonovaryOn.pow_right
@@ Mathlib.Analysis.SpecialFunctions.JapaneseBracket @@
! proof changed for finite_integral_rpow_sub_one_pow_aux
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for MonovaryOn.nsmul_right
@@ Mathlib.Algebra.Order.Field.Basic @@
! proof changed for one_div_pow_lt_one_div_pow_of_lt
@@ Mathlib.NumberTheory.RamificationInertia @@
! proof changed for Ideal.ramificationIdx_spec
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Monovary.pow_right
! proof changed for AntivaryOn.pow_left₀
@@ Mathlib.Analysis.NormedSpace.Multilinear.Basic @@
! proof changed for ContinuousMultilinearMap.continuous_eval
@@ Mathlib.Analysis.Calculus.Taylor @@
! proof changed for taylor_mean_remainder_bound
@@ Mathlib.RingTheory.Etale @@
! proof changed for Algebra.FormallySmooth.of_split
@@ Mathlib.Analysis.Complex.UpperHalfPlane.Metric @@
! proof changed for UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_mono_left
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for sq_le_sq
@@ Mathlib.Data.Num.Lemmas @@
! proof changed for Num.castNum_shiftRight
@@ Mathlib.Data.Nat.Size @@
! proof changed for Nat.size_shiftLeft'
@@ Mathlib.RingTheory.Finiteness @@
! proof changed for Ideal.exists_radical_pow_le_of_fg
@@ Mathlib.Analysis.Analytic.Inverse @@
! proof changed for FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos
@@ Mathlib.NumberTheory.Padics.RingHoms @@
! proof changed for PadicInt.appr_lt
@@ Mathlib.Data.Nat.Factorization.Basic @@
! proof changed for Nat.Ico_filter_pow_dvd_eq
@@ Mathlib.Order.Filter.Archimedean @@
! proof changed for Filter.Tendsto.atTop_nsmul_const
@@ Mathlib.Data.Real.Pi.Leibniz @@
! proof changed for Real.tendsto_sum_pi_div_four
@@ Mathlib.Analysis.Calculus.BumpFunction.Normed @@
! proof changed for ContDiffBump.measure_closedBall_div_le_integral
@@ Mathlib.Analysis.NormedSpace.Star.Multiplier @@
! proof changed for DoubleCentralizer.instCstarRing
@@ Mathlib.Analysis.NormedSpace.Multilinear.Basic @@
! proof changed for MultilinearMap.continuous_of_bound
@@ Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma @@
! proof changed for szemeredi_regularity
@@ Mathlib.Analysis.InnerProductSpace.Rayleigh @@
! proof changed for IsSelfAdjoint.linearly_dependent_of_isLocalExtrOn
@@ Mathlib.NumberTheory.ModularForms.JacobiTheta.Basic @@
! proof changed for exists_summable_bound_exp_mul_sq
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for sq_le_one_iff
@@ Mathlib.Analysis.SpecificLimits.Basic @@
! proof changed for tendsto_pow_atTop_nhds_0_iff
! proof changed for summable_one_div_pow_of_le
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_four_le_pow_two_of_pow_two_le
@@ Mathlib.Analysis.SpecialFunctions.Pow.Continuity @@
! proof changed for NNReal.eventually_pow_one_div_le
@@ Mathlib.Computability.AkraBazzi.GrowsPolynomially @@
! proof changed for AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_nonneg_or_nonpos
@@ Mathlib.NumberTheory.RamificationInertia @@
! proof changed for Ideal.quotientToQuotientRangePowQuotSucc_surjective
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for AntivaryOn.nsmul_left
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for one_lt_sq_iff
@@ Mathlib.NumberTheory.Multiplicity @@
! proof changed for multiplicity.Nat.pow_sub_pow
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.one_lt_pow'
@@ Mathlib.Analysis.Analytic.Constructions @@
! proof changed for formalMultilinearSeries_geometric_radius
@@ Mathlib.NumberTheory.Padics.PadicVal @@
! proof changed for range_pow_padicValNat_subset_divisors'
@@ Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots @@
! proof changed for IsPrimitiveRoot.sub_one_norm_two
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for MonovaryOn.pow_left₀
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.lt_of_pow_dvd_right
@@ Mathlib.Data.Polynomial.Degree.CardPowDegree @@
! proof changed for Polynomial.cardPowDegree_apply
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for LucasLehmer.residue_eq_zero_iff_sMod_eq_zero
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for sq_eq_sq_iff_abs_eq_abs
@@ Mathlib.Algebra.GroupPower.Lemmas @@
! proof changed for zpow_lt_zpow_iff
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Monovary.pow_left₀
@@ Mathlib.Algebra.Order.Field.Basic @@
! proof changed for one_div_pow_le_one_div_pow_of_le
@@ Mathlib.RingTheory.Artinian @@
! proof changed for IsArtinianRing.isNilpotent_jacobson_bot
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for one_le_sq_iff
@@ Mathlib.RingTheory.Ideal.Operations @@
! proof changed for Ideal.pow_le_self
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Monovary.nsmul_right
@@ Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology @@
! proof changed for is_ideal_adic_pow
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.log_eq_iff
@@ Mathlib.RingTheory.Polynomial.Cyclotomic.Expand @@
! proof changed for Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP
@@ Mathlib.Analysis.Analytic.Basic @@
! proof changed for HasFPowerSeriesOnBall.uniform_geometric_approx
@@ Mathlib.RingTheory.Perfection @@
! proof changed for PreTilt.valAux_add
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for AntivaryOn.pow_right
@@ Mathlib.RingTheory.Valuation.Integral @@
! proof changed for Valuation.Integers.mem_of_integral
@@ Mathlib.NumberTheory.Multiplicity @@
! proof changed for Nat.two_pow_sub_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Right.pow_nonneg
@@ Mathlib.Analysis.Normed.Field.Basic @@
! proof changed for norm_map_one_of_pow_eq_one
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for one_lt_mersenne
@@ Mathlib.Combinatorics.SetFamily.Kleitman @@
! proof changed for Finset.card_biUnion_le_of_intersecting
@@ Mathlib.Algebra.Homology.LocalCohomology @@
! proof changed for localCohomology.Ideal.exists_pow_le_of_le_radical_of_fG
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Left.pow_nonneg
@@ Mathlib.Analysis.BoxIntegral.Basic @@
! proof changed for BoxIntegral.HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO
@@ Mathlib.NumberTheory.RamificationInertia @@
! proof changed for Ideal.ramificationIdx_lt
@@ Mathlib.Data.Nat.Factorial.Basic @@
! proof changed for Nat.factorial_mul_pow_sub_le_factorial
@@ Mathlib.RingTheory.DedekindDomain.Ideal @@
! proof changed for Ideal.pow_succ_lt_pow
@@ Mathlib.NumberTheory.Liouville.LiouvilleNumber @@
! proof changed for LiouvilleNumber.aux_calc
@@ Mathlib.Analysis.Distribution.SchwartzSpace @@
! proof changed for Function.HasTemperateGrowth.norm_iteratedFDeriv_le_uniform_aux
@@ Mathlib.Data.Nat.Factorial.Basic @@
! proof changed for Nat.pow_sub_le_descFactorial
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_dvd_pow_iff_le_right
@@ Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology @@
! proof changed for Ideal.adic_basis
@@ Mathlib.Combinatorics.Additive.PluenneckeRuzsa @@
! proof changed for Finset.card_nsmul_sub_nsmul_le
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Monovary.nsmul_left
@@ Mathlib.Combinatorics.Additive.Behrend @@
! proof changed for Behrend.sum_sq_le_of_mem_box
@@ Mathlib.MeasureTheory.Group.AddCircle @@
! proof changed for AddCircle.isAddFundamentalDomain_of_ae_ball
@@ Mathlib.GroupTheory.Schreier @@
! proof changed for Subgroup.card_commutator_le_of_finite_commutatorSet
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.log_anti_left
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Monotone.pow_right
@@ Mathlib.Data.Nat.Factorial.Basic @@
! proof changed for Nat.ascFactorial_le_pow_add
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for MonovaryOn.pow_left
@@ Mathlib.Data.Complex.Exponential @@
! proof changed for Real.one_sub_div_pow_le_exp_neg
@@ Mathlib.Analysis.SpecificLimits.FloorPow @@
! proof changed for mul_pow_le_nat_floor_pow
@@ Mathlib.Topology.UnitInterval @@
! proof changed for Set.Icc.monotone_addNSMul
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_lt_self_of_lt_one
@@ Mathlib.Order.Filter.AtTopBot @@
! proof changed for Filter.Tendsto.nsmul_atTop
@@ Mathlib.Topology.EMetricSpace.Paracompact @@
! proof changed for EMetric.instParacompactSpace
@@ Mathlib.FieldTheory.Finite.Basic @@
! proof changed for FiniteField.X_pow_card_pow_sub_X_ne_zero
@@ Mathlib.Probability.StrongLaw @@
! proof changed for ProbabilityTheory.strong_law_aux1
@@ Mathlib.RingTheory.QuotientNilpotent @@
! proof changed for Ideal.IsNilpotent.induction_on
@@ Mathlib.Combinatorics.Additive.Behrend @@
! proof changed for Behrend.le_N
@@ Mathlib.Analysis.Convex.SpecificFunctions.Deriv @@
! proof changed for strictConvexOn_pow
@@ Mathlib.Data.Real.Pi.Bounds @@
! proof changed for Real.pi_lt_sqrtTwoAddSeries
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for sq_eq_sq
@@ Mathlib.Analysis.Calculus.FDeriv.Measurable @@
! proof changed for FDerivMeasurableAux.D_subset_differentiable_set
@@ Mathlib.NumberTheory.Divisors @@
! proof changed for Nat.mem_properDivisors_prime_pow
@@ Mathlib.Algebra.GroupPower.Lemmas @@
! proof changed for zpow_lt_zpow
@@ Mathlib.Data.Nat.Squarefree @@
! proof changed for Nat.sq_mul_squarefree_of_pos
@@ Mathlib.Combinatorics.SimpleGraph.Regularity.Increment @@
! proof changed for SzemerediRegularity.card_increment
@@ Mathlib.Data.Polynomial.Degree.CardPowDegree @@
! proof changed for Polynomial.cardPowDegree
@@ Mathlib.NumberTheory.FermatPsp @@
! proof changed for Nat.exists_infinite_pseudoprimes
@@ Mathlib.Analysis.Analytic.Basic @@
! proof changed for HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
@@ Mathlib.RingTheory.DedekindDomain.Ideal @@
! proof changed for Ideal.exists_mem_pow_not_mem_pow_succ
@@ Mathlib.Combinatorics.Additive.Behrend @@
! proof changed for Behrend.dValue_pos
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for lt_of_mul_self_lt_mul_self
@@ Mathlib.Topology.MetricSpace.HausdorffDistance @@
! proof changed for IsOpen.exists_iUnion_isClosed
@@ Mathlib.NumberTheory.RamificationInertia @@
! proof changed for Ideal.quotientToQuotientRangePowQuotSucc_injective
@@ Mathlib.Data.Polynomial.Degree.Lemmas @@
! proof changed for Polynomial.natDegree_comp_le
@@ Mathlib.Data.Complex.Exponential @@
! proof changed for Real.sinh_lt_cosh
@@ Mathlib.Data.Nat.Choose.Factorization @@
! proof changed for Nat.factorization_choose_of_lt_three_mul
@@ Mathlib.Data.Real.ENNReal @@
! proof changed for ENNReal.zpow_le_of_le
@@ Mathlib.Topology.UnitInterval @@
! proof changed for Set.Icc.addNSMul_eq_right
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for Left.pow_le_one_of_le
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.log_le_clog
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Antivary.pow_left₀
@@ Mathlib.Data.Nat.Log @@
! proof changed for Nat.clog_pow
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for Antivary.nsmul_left
@@ Mathlib.NumberTheory.Padics.RingHoms @@
! proof changed for PadicInt.nthHomSeq_one
@@ Mathlib.Analysis.SpecificLimits.Basic @@
! proof changed for tendsto_add_one_pow_atTop_atTop_of_pos
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for one_le_pow_of_one_le'
@@ Mathlib.Combinatorics.Additive.Behrend @@
! proof changed for Behrend.roth_lower_bound_explicit
! proof changed for Behrend.dValue
@@ Mathlib.Algebra.Order.Monovary @@
! proof changed for AntivaryOn.nsmul_right
! proof changed for Monovary.pow_left
@@ Mathlib.Data.Nat.Bitwise @@
! proof changed for Nat.append_lt
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_le_nsmul_iff_left
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.pow_left_strictMono
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_le_pow_iff_right'
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for LucasLehmer.mersenne_int_ne_zero
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_lt_nsmul_iff_left
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.one_lt_two_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_lt_pow_iff_right'
@@ Mathlib.NumberTheory.Divisors @@
! proof changed for Nat.properDivisors_prime_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for le_of_pow_le_pow_left'
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_le_one_iff_of_nonneg
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_left_strictMono
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for abs_pow_eq_one
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for nsmul_le_nsmul_left
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_left_inj
! proof changed for pow_lt_pow_iff_right_of_lt_one
@@ Mathlib.NumberTheory.Multiplicity @@
! proof changed for padicValNat.pow_two_sub_pow
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_right_strictMono'
@@ Mathlib.NumberTheory.LucasLehmer @@
! proof changed for LucasLehmer.sMod_lt
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_lt_pow_iff_right
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.one_lt_pow
@@ Mathlib.Algebra.GroupPower.Order @@
! proof changed for pow_le_pow_iff_right
! proof changed for pow_lt_one_iff_of_nonneg
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_le_pow_right_of_le_one'
@@ Mathlib.Data.Nat.Pow @@
! proof changed for Nat.one_lt_pow_iff
@@ Mathlib.Algebra.GroupPower.CovariantClass @@
! proof changed for pow_left_strictMono
366 differences
total 9.85s
```

Structure
---------

There are two test directories, both of which are independent Lean projects  that implement a module `Test`, but with slightly different content.
This can be used to test leaff like so `./runleaff Test.Test test/ test`.
