Leaff
=====

Leaff is a diff tool for Lean environments. It aims to produce a human readable summary of the differences between two versions of the same Lean module stored in olean files. For example it can be used to detect unexpected changes to, or removal of, theorems when a refactor is carried out in a large library.

It is currently under development and should be considered version alpha (contributions welcome!).
It is not currently particularly user friendly, though it is at least fast enough to run on the scale of `mathlib`.
Nevertheless at the moment it does at least provide some potentially useful output e.g.


```diff
$ lake exe leaff Mathlib $(tr ':' ',' <<<"$(eval $(lake --dir ../test-mathlib2/ env) && echo $LEAN_PATH)") $(tr ':' ',' <<<"$(eval $(lake --dir ../test-mathlib/ env) && echo $LEAN_PATH)")
Found differences:
+ added Affine.Simplex.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection
+ added Affine.Simplex.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
+ added Fin.inhabitedFinOneAdd
+ added MeasureTheory.Integrable
+ added norm_withSeminorms
+ added Module.Flat.iff_rTensor_injective'
+ added Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq
+ added Submodule.exists_fg_le_eq_rTensor_inclusion
+ added Fin.inhabited
+ added Affine.Simplex.orthogonalProjection_circumcenter
+ added Fin.default_eq_zero
+ added Fin.eq_zero
+ added Fin.uniqueFinOne
+ added EuclideanGeometry.eq_or_eq_reflection_of_dist_eq
+ added Affine.Simplex.dist_circumcenter_sq_eq_sq_sub_circumradius
- removed inhabitedFinOneAdd
- removed Affine.Simplex.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection
- removed Fin.unique
- removed Affine.Simplex.dist_circumcenter_sq_eq_sq_sub_circumradius
- removed Fin.default_eq_zero
- removed Fin.eq_zero
- removed EuclideanGeometry.eq_or_eq_reflection_of_dist_eq
- removed Affine.Simplex.orthogonalProjection_circumcenter
- removed norm_withSeminorms
- removed MeasureTheory.Integrable
- removed Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq
- removed instInhabitedFinSucc
- removed Affine.Simplex.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
! type changed for Affine.Simplex.orthogonalProjection_vadd_smul_vsub_orthogonalProjection
! type changed for Affine.Simplex.orthogonalProjectionSpan
! type changed for Affine.Simplex.orthogonalProjection_eq_circumcenter_of_dist_eq
+ direct import Mathlib.Init.Data.Fin.Basic added to Mathlib.Data.Countable.Defs
+ direct import Mathlib.Init.Data.Fin.Basic added to Mathlib.Data.Fin.Basic
+ direct import Mathlib.Init.Data.Fin.Basic added to Mathlib.Data.List.Nodup
! proof changed for FirstOrder.Language.card_functions_sum_skolem₁
! proof changed for parallelepiped_orthonormalBasis_one_dim
! proof changed for Matrix.vec_single_eq_const
! proof changed for Real.exists_rat_eq_convergent'
! proof changed for spectrum.exp_mem_exp
! proof changed for MeasureTheory.Memℒp.variance_eq
! proof changed for ProbabilityTheory.IndepFun.variance_sum
! proof changed for MeasureTheory.integrable_comp_mul_right_iff
! proof changed for Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero
! proof changed for Matrix.det_fin_two
! proof changed for sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair
! proof changed for Orientation.eq_or_eq_neg_of_isEmpty
! proof changed for MeasureTheory.integrable_comp_smul_iff
! proof changed for Memℓp.add
! proof changed for mellin_hasDerivAt_of_isBigO_rpow
! proof changed for MeasureTheory.tendsto_integral_smul_of_tendsto_average_norm_sub
! proof changed for FiniteDimensional.basisUnique
! proof changed for MeasureTheory.hasSum_integral_iUnion_ae
! proof changed for NormedField.exists_lt_nnnorm_lt
! proof changed for banach_steinhaus
! proof changed for Affine.Simplex.eq_circumcenter_of_dist_eq
! proof changed for Padic.exi_rat_seq_conv_cauchy
! proof changed for ModularGroup.T_pow_mul_apply_one
! proof changed for hasMellin_one_Ioc
! proof changed for EuclideanGeometry.Cospherical.affineIndependent_of_mem_of_ne
! proof changed for AlgebraicTopology.DoldKan.HigherFacesVanish.induction
! proof changed for MeasureTheory.integrable_finset_sum
! proof changed for MeasureTheory.Integrable.div_const
! proof changed for ENNReal.rpow_arith_mean_le_arith_mean2_rpow
! proof changed for MeasureTheory.integral_sub_average
! proof changed for Orientation.rotation_eq_matrix_toLin
! proof changed for Cardinal.power_one
! proof changed for MeasureTheory.integrableOn_empty
! proof changed for FirstOrder.Language.Formula.realize_rel₂
! proof changed for WittVector.select_add_select_not
! proof changed for NormedSpace.equicontinuous_TFAE
! proof changed for Real.toNNReal_eq_nat_cast
! proof changed for FinVec.sum_eq
! proof changed for Matrix.mul_fin_three
! proof changed for hasDerivAt_integral_of_dominated_loc_of_lip
! proof changed for MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
! proof changed for torusIntegral_dim1
! proof changed for Affine.Simplex.circumcenter_eq_point
! proof changed for bernsteinPolynomial.derivative_succ_aux
! proof changed for Basis.eq_bot_of_rank_eq_zero
! proof changed for Seminorm.cont_withSeminorms_normedSpace
! proof changed for integrable_mul_exp_neg_mul_sq
! proof changed for QuaternionAlgebra.instNontrivialQuaternionAlgebra
! proof changed for convolution_assoc
! proof changed for FormalMultilinearSeries.rightInv_coeff
! proof changed for GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I
! proof changed for MeasureTheory.set_integral_prod
! proof changed for Int.lt_of_sum_four_squares_eq_mul
! proof changed for HasFTaylorSeriesUpToOn.hasFDerivWithinAt
! proof changed for MeasureTheory.IntegrableOn.smul_continuousOn
! proof changed for Cardinal.instNontrivialCardinal
! proof changed for HomotopyGroup.pi1EquivFundamentalGroup
! proof changed for MeasureTheory.integrable_finset_sum_measure
! proof changed for MeasureTheory.exists_upperSemicontinuous_lt_integral_gt
! proof changed for GeneralizedContinuedFraction.abs_sub_convergents_le
! proof changed for IsCyclotomicExtension.discr_prime_pow
! proof changed for exists_linearIndependent_pair_of_one_lt_rank
! proof changed for ProbabilityTheory.measure_le_le_exp_mul_mgf
! proof changed for ProbabilityTheory.condCdf'
! proof changed for MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
! proof changed for IsNoetherianRing.strongRankCondition
! proof changed for MeasureTheory.integral_eq_of_hasDerivWithinAt_off_countable_of_le
! proof changed for GeneralizedContinuedFraction.of_convergence_epsilon
! proof changed for linearIndependent_fin2
! proof changed for Affine.Simplex.reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter
! proof changed for MeasureTheory.Integrable.comp_div_right
! proof changed for banach_steinhaus_iSup_nnnorm
! proof changed for NNReal.rpow_arith_mean_le_arith_mean2_rpow
! proof changed for MeasurableSpace.cardinal_generateMeasurable_le_continuum
! proof changed for MeasureTheory.Integrable.prod_smul
! proof changed for not_disjoint_segment_convexHull_triple
! proof changed for Orientation.volumeForm_robust'
! proof changed for ProbabilityTheory.iIndepFun.integrable_exp_mul_sum
! proof changed for Behrend.box_zero
! proof changed for FirstOrder.Language.Term.realize_functions_apply₂
! proof changed for MeasureTheory.memℒp_two_iff_integrable_sq
! proof changed for ProbabilityTheory.variance_def'
! proof changed for SimpleGraph.pathGraph_connected
! proof changed for groupCohomology.dOne_comp_eq
! proof changed for MeasureTheory.integrable_smul_measure
! proof changed for Affine.Simplex.circumsphere_unique_dist_eq
! proof changed for Cardinal.one_power
! proof changed for Module.Flat.iff_rTensor_injective
! proof changed for SzemerediRegularity.card_biUnion_star_le_m_add_one_card_star_mul
! proof changed for MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_aux₂
! proof changed for Affine.Simplex.eq_circumradius_of_dist_eq
! proof changed for MeasureTheory.setToFun_finset_sum'
! proof changed for Seminorm.cont_normedSpace_to_withSeminorms
! proof changed for MeasureTheory.integrable_average
! proof changed for MeasureTheory.integrableOn_map_equiv
! proof changed for MeasureTheory.Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part
! proof changed for ProbabilityTheory.IndepFun.integrable_exp_mul_add
! proof changed for MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivWithinAt_off_countable_of_le
! proof changed for groupCohomology.dZero_comp_eq
! proof changed for MeasureTheory.IntegrableOn.continuousOn_smul
! proof changed for MeasureTheory.Integrable.convolution_integrand
! proof changed for Cardinal.mk_eq_one
! proof changed for Pell.exists_of_not_isSquare
! proof changed for MeasureTheory.Measure.haar.addPrehaar_mono
! proof changed for Fin.sum_univ_one
! proof changed for Cardinal.lift_one
! proof changed for Besicovitch.exists_goodδ
! proof changed for MeasureTheory.integrable_comp_div_left
! proof changed for HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
! proof changed for finOneEquiv
! proof changed for groupCohomology.oneCochainsLequiv
! proof changed for MeasureTheory.Memℒp.integrable_norm_rpow'
! proof changed for Fin.prod_univ_one
! proof changed for MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
! proof changed for FiniteField.X_pow_card_sub_X_natDegree_eq
! proof changed for MeasureTheory.Integrable.simpleFunc_mul
! proof changed for convolutionExistsAt_flip
! proof changed for MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero
! proof changed for ZMod.instUnique
! proof changed for MeasureTheory.Integrable.sub
! proof changed for integrable_exp_neg_mul_sq
! proof changed for FirstOrder.Language.BoundedFormula.realize_rel₂
! proof changed for ConvolutionExistsAt.integrable_swap
! proof changed for MeasureTheory.Measure.haar.prehaar_mono
! proof changed for Orientation.abs_areaForm_le
! proof changed for EuclideanSpace.volume_ball
! proof changed for ProbabilityTheory.integrable_gaussianPdfReal
! proof changed for ProbabilityTheory.condCdf'_def
! proof changed for Matrix.det_fin_one
! proof changed for MeasureTheory.integral_fintype
! proof changed for Fin.sum_univ_two
! proof changed for Orientation.abs_areaForm_of_orthogonal
! proof changed for MeasurableEmbedding.integrableOn_map_iff
! proof changed for Mathlib.Meta.NormNum.isRat_eq_false
! proof changed for integral_mul_cpow_one_add_sq
! proof changed for Fin.prod_univ_two
! proof changed for VectorFourier.fourier_integral_convergent_iff
! proof changed for NormedSpace.toLocallyConvexSpace'
! proof changed for Rat.numberField_discr
! proof changed for Matrix.mul_fin_two
! proof changed for Orientation.areaForm_le
! proof changed for Matrix.det_fin_three
! proof changed for Action.diagonalOneIsoLeftRegular
! proof changed for MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt
! proof changed for catalan_one
! proof changed for MeasureTheory.Submartingale.sum_mul_upcrossingStrat_le
- direct import Mathlib.Init.Data.Fin.Basic removed from Mathlib.Logic.Unique
181 differences
total 6.29s
```
