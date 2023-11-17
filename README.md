Leaff
=====

Leaff is a diff tool for Lean environments.
It is currently under development and should be considered version alpha.
It is not currently particularly user friendly, though it is at least fast enough to run on the scale of `mathlib`.
Nevertheless at the moment it does at least provide some potentially useful output e.g.


```
(base) alexanderbest@nmslap008245:~/leaff$ lake exe leaff Mathlib "lake-packages/mathlib//lake-packages/std/build/lib","lake-packages/mathlib//lake-packages/Qq/build/lib","lake-packages/mathlib//lake-packages/aesop/build/lib","lake-packages/mathlib//lake-packages/Cli/build/lib","lake-packages/mathlib//lake-packages/proofwidgets/build/lib","lake-packages/mathlib//build/lib","/home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.3.0-rc1/lib/lean" "lake-packages/mathlib2//lake-packages/std/build/lib","lake-packages/mathlib2//lake-packages/Qq/build/lib","lake-packages/mathlib2//lake-packages/aesop/build/lib","lake-packages/mathlib2//lake-packages/Cli/build/lib","lake-packages/mathlib2//lake-packages/proofwidgets/build/lib","lake-packages/mathlib2//build/lib","/home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.3.0-rc1/lib/lean"
info: [336/336] Linking leaff
newModule: Mathlib
oldModule: Mathlib
#[lake-packages/mathlib2//lake-packages/std/build/lib, lake-packages/mathlib2//lake-packages/Qq/build/lib, lake-packages/mathlib2//lake-packages/aesop/build/lib, lake-packages/mathlib2//lake-packages/Cli/build/lib, lake-packages/mathlib2//lake-packages/proofwidgets/build/lib, lake-packages/mathlib2//build/lib, /home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.3.0-rc1/lib/lean]
#[lake-packages/mathlib//lake-packages/std/build/lib, lake-packages/mathlib//lake-packages/Qq/build/lib, lake-packages/mathlib//lake-packages/aesop/build/lib, lake-packages/mathlib//lake-packages/Cli/build/lib, lake-packages/mathlib//lake-packages/proofwidgets/build/lib, lake-packages/mathlib//build/lib, /home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.3.0-rc1/lib/lean]
[lake-packages/mathlib//lake-packages/std/build/lib, lake-packages/mathlib//lake-packages/Qq/build/lib, lake-packages/mathlib//lake-packages/aesop/build/lib, lake-packages/mathlib//lake-packages/Cli/build/lib, lake-packages/mathlib//lake-packages/proofwidgets/build/lib, lake-packages/mathlib//build/lib, /home/alexanderbest/.elan/toolchains/leanprover--lean4---v4.3.0-rc1/lib/lean]
hashes1 made
hashes2 made
diffs made
174
comps
Found differences:
added IsAlgebraic.larger_base
added Algebra.IsIntegral.of_finite
added RingHom.IsIntegralElem.sub
added Algebra.IsAlgebraic.trans
added RingHom.isIntegralElem_map
added RingHom.IsIntegral.quotient
added IsIntegral.of_finite
added Algebra.IsAlgebraic.larger_base
added IsAlgClosed.lift_def
added Algebra.IsIntegral.trans
added Algebra.isIntegral_of_surjective
added IsIntegral.of_mem_closure''
added RingHom.IsIntegral.trans
added IsIntegral.of_mem_of_fg
added IsIntegral.map_of_comp_eq
added IsIntegral.smul
added IsIntegral.tower_top
added Algebra.isIntegral_sup
added IsIntegral.of_mem_closure'
added integralClosure_map_algEquiv
added RingHom.isIntegralElem_zero
added RingHom.IsIntegral.tower_top
added IsIntegralClosure.mk'_one
added IsIntegral.of_mul_unit
added Algebra.lmul_injective
added isIntegral_trans
added Polynomial.scaleRoots_aeval_eq_zero
added IsAlgebraic.isIntegral
added IsIntegral.zsmul
added IsIntegral.neg
added Algebra.IsIntegral.isField_iff_isField
added isIntegral_algebraMap_iff
added IsIntegralClosure.mk'_zero
added RingHom.IsIntegralElem.of_mem_closure
added IsIntegral.algebraMap
added Algebra.IsAlgebraic.of_finite
added Polynomial.scaleRoots_eval₂_mul_of_commute
added RingHom.IsIntegralElem.of_mul_unit
added Algebra.IsIntegral.isAlgebraic
added RingHom.IsIntegralElem.add
added Algebra.IsAlgebraic.larger_base_of_injective
added isIntegral_iff_isIntegral_closure_finite
added IsIntegral.pow
added RingHom.IsIntegralElem.neg
added isIntegral_zero
added RingHom.isIntegralElem.of_comp
added isIntegral_one
added RingHom.IsIntegralElem.mul
added IsIntegral.tower_bot
added IsAlgebraic.larger_base_of_injective
added IsIntegral.nsmul
added IsIntegral.of_pow
added IsIntegral.tmul
added IsIntegral.fg_adjoin_singleton
added RingHom.isIntegralElem_one
added Algebra.IsAlgebraic.isIntegral
added isField_of_isIntegral_of_isField
added IsIntegral.of_subring
added RingHom.IsIntegral.tower_bot
added IsSepClosed.lift_def
removed Algebra.IsIntegral.isField_iff_isField
removed IsIntegral.of_pow
removed Algebra.isIntegral_of_finite
removed IsIntegral.smul
removed RingHom.is_integral_neg
removed isIntegral_of_mem_closure'
removed IsAlgebraic.of_larger_base_of_injective
removed Algebra.IsIntegral.of_finite
removed IsIntegral.of_subring
removed RingHom.is_integral_mul
removed RingHom.isIntegral_of_isIntegral_mul_unit
removed IsIntegral.of_mul_unit
removed IsIntegral.pow
removed IsAlgClosed.lift_def
removed RingHom.is_integral_sub
removed IsIntegral.tmul
removed RingHom.isIntegral_trans
removed Algebra.isIntegral_trans
removed RingHom.isIntegralElem_of_isIntegralElem_comp
removed IsIntegral.zsmul
removed isIntegral_trans
removed IsIntegral.algebraMap
removed IsIntegral.map_of_comp_eq
removed isIntegral_one
removed RingHom.is_integral_map
removed Algebra.isAlgebraic_of_larger_base
removed isIntegral_of_isScalarTower
removed integralClosure_map_algEquiv
removed isIntegral_iff_isIntegral_closure_finite
removed Algebra.isAlgebraic_trans
removed RingHom.isIntegral_quotient_of_isIntegral
removed isField_of_isIntegral_of_isField
removed isIntegral_sup
removed isIntegral_trans_aux
removed IsIntegral.of_finite
removed IsIntegral.nsmul
removed isIntegral_of_surjective
removed RingHom.isIntegral_tower_top_of_isIntegral
removed Polynomial.scaleRoots_aeval_eq_zero
removed RingHom.is_integral_of_mem_closure
removed isIntegral_tower_top_of_isIntegral
removed IsIntegralClosure.mk'_zero
removed RingHom.is_integral_zero
removed Algebra.isAlgebraic_of_finite
removed RingHom.isIntegral_tower_bot_of_isIntegral
removed IsIntegral.of_mem_of_fg
removed IsAlgebraic.of_larger_base
removed isIntegral_of_mem_closure''
removed Algebra.isAlgebraic_of_larger_base_of_injective
removed IsIntegral.fg_adjoin_singleton
removed RingHom.is_integral_one
removed IsIntegral.tower_bot
removed isIntegral_algebraMap_iff
removed IsIntegralClosure.mk'_one
removed isIntegral_zero
removed IsIntegral.neg
removed RingHom.is_integral_add
removed IsSepClosed.lift_def
type changed for IsPrimitiveRoot.subOnePowerBasis_dim
type changed for IsPrimitiveRoot.subOnePowerBasis_gen
renamed IsAlgebraic.of_larger_base_of_injective → IsAlgebraic.larger_base_of_injective
renamed RingHom.isIntegral_quotient_of_isIntegral → RingHom.IsIntegral.quotient
renamed RingHom.is_integral_map → RingHom.isIntegralElem_map
renamed isIntegral_of_surjective → Algebra.isIntegral_of_surjective
proof changed for AlgebraicClosureAux.isAlgebraic
proof changed for IntermediateField.Lifts.exists_lift_of_splits
proof changed for IsPrimitiveRoot.subOnePowerBasis
proof changed for Ideal.Polynomial.comp_C_integral_of_surjective_of_jacobson
proof changed for Algebra.discr_mul_isIntegral_mem_adjoin
proof changed for isIntegral_algEquiv
proof changed for IsFractionRing.isAlgebraic_iff'
proof changed for Polynomial.lift_of_splits
proof changed for Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
proof changed for PowerBasis.toMatrix_isIntegral
proof changed for Normal.of_isSplittingField
proof changed for Polynomial.IsSplittingField.finiteDimensional
proof changed for isIntegral_of_submodule_noetherian
proof changed for Field.finiteDimensional_of_finite_intermediateField
proof changed for mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
proof changed for isIntegral_quotientMap_iff
proof changed for Normal.isIntegral
proof changed for IsIntegralClosure.range_le_span_dualBasis
proof changed for le_integralClosure_iff_isIntegral
proof changed for ax_grothendieck_of_locally_finite
proof changed for RingHom.isIntegral_respectsIso
proof changed for IntermediateField.adjoin_minpoly_coeff_of_exists_primitive_element
proof changed for IsSepClosed.lift
proof changed for IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
proof changed for Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly
proof changed for IntermediateField.exists_finset_of_mem_supr''
proof changed for Algebra.isIntegral_trace
proof changed for integralClosure
proof changed for IsGalois.of_separable_splitting_field
proof changed for IntermediateField.isAlgebraic_adjoin_simple
proof changed for IsIntegral.sub
proof changed for IsIntegralClosure.isIntegral
proof changed for isIntegral_of_noetherian
proof changed for ClassGroup.fintypeOfAdmissibleOfFinite
proof changed for AdjoinRoot.isIntegral_root
proof changed for Normal.of_algEquiv
proof changed for IntermediateField.AdjoinSimple.trace_gen_eq_zero
proof changed for FunctionField.ringOfIntegers.not_isField
proof changed for Field.finite_intermediateField_of_exists_primitive_element
proof changed for NumberField.isAlgebraic
proof changed for Algebra.adjoin.powerBasisAux
proof changed for normalizeScaleRoots_support
proof changed for IntermediateField.AdjoinSimple.norm_gen_eq_one
proof changed for IsIntegral.tower_bot_of_field
proof changed for Ideal.Polynomial.isIntegral_isLocalization_polynomial_quotient
proof changed for RingHom.isIntegral_of_surjective
proof changed for IsIntegral.pow_iff
proof changed for isField_of_isIntegral_of_isField'
proof changed for mem_integralClosure_iff_mem_fg
proof changed for mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt
proof changed for Algebra.isAlgebraic_iff_isIntegral
proof changed for Algebra.IsIntegral
proof changed for RingHom.isIntegralElem_leadingCoeff_mul
proof changed for RingHom.Finite.to_isIntegral
proof changed for IsIntegral.add
proof changed for Polynomial.Gal.prime_degree_dvd_card
proof changed for IsIntegralClosure.exists_smul_eq_mul
proof changed for minpoly.natDegree_le
proof changed for IsIntegralClosure.isFractionRing_of_finite_extension
proof changed for FractionalIdeal.isFractional_adjoin_integral
proof changed for minpoly.dvd
proof changed for IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime_pow
proof changed for IsIntegral.of_mem_closure
proof changed for NumberField.Embeddings.pow_eq_one_of_norm_eq_one
proof changed for Algebra.IsIntegral.finite
proof changed for IntermediateField.isAlgebraic_iSup
proof changed for Ideal.MvPolynomial.comp_C_integral_of_surjective_of_jacobson
proof changed for IsAlgClosed.algebraMap_surjective_of_isAlgebraic
proof changed for PowerBasis.repr_gen_pow_isIntegral
proof changed for PowerBasis.repr_pow_isIntegral
proof changed for isIntegral_algebraMap
proof changed for Algebra.IsIntegral.quotient
proof changed for RingHom.IsIntegral.to_finite
proof changed for Normal.tower_top_of_normal
proof changed for IsAlgClosure.ofAlgebraic
proof changed for dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_isEisensteinAt
proof changed for IsIntegral.mul
proof changed for AlgHom.bijective
proof changed for RingHom.isIntegral_stableUnderComposition
proof changed for IsIntegral.det
proof changed for IsIntegralClosure.isDedekindDomain
proof changed for IntermediateField.AdjoinSimple.isIntegral_gen
proof changed for leadingCoeff_smul_normalizeScaleRoots
proof changed for isSeparable_tower_top_of_isSeparable
proof changed for RingHom.isIntegral_stableUnderBaseChange
proof changed for Ideal.Polynomial.jacobson_bot_of_integral_localization
proof changed for Algebra.isIntegral_norm
proof changed for isIntegral_algHom_iff
proof changed for IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
proof changed for isIntegral_localization
proof changed for integralClosure_idem
proof changed for RingOfIntegers.isUnit_norm
proof changed for IsAlgClosed.lift
proof changed for fg_adjoin_of_finite
proof changed for IntermediateField.sup_toSubalgebra
proof changed for normalClosure.restrictScalars_eq_iSup_adjoin
proof changed for IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one
proof changed for IsGalois.of_separable_splitting_field_aux
proof changed for NumberField.RingOfIntegers.not_isField
proof changed for solvableByRad.isIntegral
proof changed for IsIntegralClosure.algebraMap_lift
proof changed for exists_integral_multiples
proof changed for Algebra.finite_iff_isIntegral_and_finiteType
proof changed for AlgebraicClosure.Step.isIntegral
proof changed for Ideal.Polynomial.quotient_mk_comp_C_isIntegral_of_jacobson
proof changed for Polynomial.scaleRoots_eval₂_mul
proof changed for adjoin_le_integralClosure
proof changed for IsAlgebraic.of_finite
proof changed for minpoly.ne_zero_of_finite
proof changed for normalizeScaleRoots_coeff_mul_leadingCoeff_pow
proof changed for Field.finiteDimensional_of_exists_primitive_element
proof changed for RingOfIntegers.isUnit_norm_of_isGalois
236 differences, some not shown
total 22.7s
```
