Leaff
=====

Leaff is a diff tool for Lean environments. It aims to produce a human readable summary of the differences between two versions of the same Lean module stored in olean files. For example it can be used to detect unexpected changes to, or removal of, theorems when a refactor is carried out in a large library.

It is currently under development and should be considered version alpha (contributions welcome!).
It is not currently particularly user friendly, though it is at least fast enough to run on the scale of `mathlib`.
Nevertheless at the moment it does at least provide some potentially useful output e.g.


```diff
$ lake exe leaff Mathlib $(tr ':' ',' <<<"$(eval $(lake --dir ../test-mathlib2/ env) && echo $LEAN_PATH)") $(tr ':' ',' <<<"$(eval $(lake --dir ../test-mathlib/ env) && echo $LEAN_PATH)")
hashes1 made
hashes2 made
diffs made
231
comps
Found differences:
+ added Algebra.IsAlgebraic.algHomEmbeddingOfSplits
+ added Finset.diag_mem_sym2_mem_iff
+ added List.Nodup.sym
+ added AlgHom.map_fieldRange
+ added Lean.Expr.getAppApps
+ added LieIdeal.coe_inclusion
+ added LieIdeal.inclusion_injective
+ added Algebra.IsAlgebraic.isNormalClosure_iff
+ added Finset.Nonempty.sym2
+ added normalClosure.algHomEquiv
+ added Finset.strictMono_sym2
+ added IsNormalClosure.equiv
+ added LieSubmodule.inclusion_apply
+ added Lean.Expr.relSidesIfRefl?
+ added List.mk_mem_sym2_iff
+ added CochainComplex.shiftFunctor_map_f
+ added List.length_sym
+ added Multiset.mem_sym2_iff
+ added Submodule.coe_inclusion
+ added List.sym2_eq_nil_iff
+ added IsNormalClosure.lift
+ added isSplittingField_iff_intermediateField
+ added List.Subperm.sym2
+ added LinearPMap.apply_comp_inclusion
+ added Finset.sym2_eq_empty
+ added Finset.sym2_eq_image
+ added normalClosure_eq_iSup_adjoin'
+ added LieIdeal.inclusion
+ added Lean.Expr.reduceProjStruct?
+ added Sym2.instFintype
+ added Submodule.inclusion
+ added Finset.image_diag_union_image_offDiag
+ added LieIdeal.inclusion_apply
+ added Finset.sym2_empty
+ added List.sym
+ added LieSubalgebra.coe_inclusion
+ added Algebra.IsAlgebraic.isNormalClosure_normalClosure
+ added List.left_mem_of_mk_mem_sym2
+ added Multiset.card_sym2
+ added LieSubmodule.coe_inclusion
+ added IntermediateField.gc_map_comap
+ added List.sym_sublist_sym_cons
+ added Submodule.subtype_comp_inclusion
+ added Submodule.range_inclusion
+ added IsNormalClosure.adjoin_rootSet
+ added Algebra.IsAlgebraic.normalClosure_eq_iSup_adjoin_of_splits
+ added List.sym_map
+ added CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_inv_app
+ added Sym.not_mem_nil
+ added IntermediateField.splits_of_mem_adjoin
+ added List.length_sym2
+ added IsNormalClosure.splits
+ added Multiset.monotone_sym2
+ added normalClosure.normal
+ added List.mem_sym2_cons_iff
+ added IntermediateField.map_sup
+ added Multiset.nodup_map_iff_of_injective
+ added IntermediateField.map_le_iff_le_comap
+ added CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_hom_app
+ added LieSubalgebra.inclusion
+ added Finset.sym2_mono
+ added IsNormalClosure.recOn
+ added Finset.sym2
+ added List.Perm.sym2
+ added Submodule.ker_inclusion
+ added Finset.sym2_toFinset
+ added Multiset.Nodup.sym2
+ added List.nodup_iff_count_eq_one
+ added List.sym_one_eq
+ added LieSubalgebra.inclusion_apply
+ added Finset.monotone_sym2
+ added Finset.injective_sym2
+ added Finset.sym2_singleton
+ added Finset.sym2_nonempty
+ added Submodule.inclusion_apply
+ added Multiset.sym2_coe
+ added Multiset.sym2_mono
+ added List.sym2_eq_sym_two
+ added Finset.diag_mem_sym2_iff
+ added List.mem_sym2_iff
+ added UniqueFactorizationMonoid.mem_normalizedFactors_iff
+ added LieSubmodule.inclusion
+ added IsNormalClosure.casesOn
+ added Finset.card_sym2
+ added List.first_mem_of_cons_mem_sym
+ added List.sym2
+ added List.Nodup.sym2
+ added List.mk_mem_sym2
+ added Multiset.mk_mem_sym2_iff
+ added Finset.mem_sym2_iff
+ added normalClosure_eq_iSup_adjoin
+ added Multiset.nodup_iff_count_eq_one
+ added IsNormalClosure.noConfusion
+ added Multiset.nodup_map_iff_of_inj_on
+ added Finset.sym2_val
+ added Lean.Meta.pureIsDefEq
+ added LieSubalgebra.inclusion_injective
+ added Finset.not_isDiag_mk_of_mem_offDiag
+ added IsNormalClosure.noConfusionType
+ added List.Sublist.sym
+ added Sym.exists_cons_of_mem
+ added Submodule.map_subtype_range_inclusion
+ added Lean.Expr.forallNot_of_notExists
+ added Sym2.card_subtype_not_diag
+ added Multiset.sym2
+ added List.mem_of_mem_of_mem_sym
+ added Finset.sym2_univ
+ added Submodule.inclusion_injective
+ added Sym2.card_image_diag
+ added Finset.mk_mem_sym2_iff
+ added Sym2.card
+ added Linarith.isStrictIntComparison
+ added IntermediateField.comap
+ added Sym2.two_mul_card_image_offDiag
+ added Sym2.card_image_offDiag
+ added isNormalClosure_normalClosure
+ added IsNormalClosure.normal
+ added LinearMap.submoduleImage_apply_of_le
+ added LieSubmodule.inclusion_injective
+ added IsGalois.normalClosure
+ added Sym2.card_subtype_diag
+ added IntermediateField.map_iSup
+ added UniqueFactorizationMonoid.factors_pow_count_prod
+ added Lean.Expr.relSidesIfSymm?
+ added Algebra.IsAlgebraic.normalClosure_le_iSup_adjoin
+ added Lean.Meta.mkRel
+ added UniqueFactorizationMonoid.normalizedFactors_multiset_prod
+ added Finset.isDiag_mk_of_mem_diag
+ added List.Sublist.sym2
+ added Multiset.sym2_eq_zero_iff
+ added List.right_mem_of_mk_mem_sym2
- removed Finset.sym2
- removed Finset.mk'_mem_sym2_iff
- removed LieIdeal.coe_homOfLe
- removed LieIdeal.homOfLe_injective
- removed normalClosure.restrictScalars_eq_iSup_adjoin
- removed LieSubmodule.coe_homOfLe
- removed LieSubalgebra.homOfLe
- removed Submodule.subtype_comp_ofLe
- removed CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_hom_app
- removed Finset.diag_mem_sym2_iff
- removed Submodule.ofLe_injective
- removed Finset.diag_mem_sym2_mem_iff
- removed LieSubalgebra.coe_homOfLe
- removed Lean.MVarId.subsingleton?
- removed Submodule.map_subtype_range_ofLe
- removed Submodule.ofLe
- removed LinearPMap.apply_comp_ofLe
- removed Lean.MVarId.independent?
- removed Linarith.isStrictIntComparison
- removed Finset.card_sym2
- removed LinearMap.submoduleImage_apply_ofLe
- removed Submodule.coe_ofLe
- removed IsGalois.normalClosure
- removed Submodule.range_ofLe
- removed Finset.sym2_empty
- removed Finset.image_diag_union_image_offDiag
- removed Sym2.two_mul_card_image_offDiag
- removed AlgHom.map_fieldRange
- removed Finset.nonempty.sym2
- removed Finset.not_isDiag_mk'_of_mem_offDiag
- removed LieSubmodule.homOfLe_injective
- removed Sym2.card_subtype_diag
- removed Finset.mem_sym2_iff
- removed Submodule.ofLe_apply
- removed normalClosure.normal
- removed LieIdeal.homOfLe
- removed CategoryTheory.Pretriangulated.shiftFunctorAdd'_op_inv_app
- removed LieIdeal.homOfLe_apply
- removed Sym2.card_image_diag
- removed Sym2.card_subtype_not_diag
- removed LieSubmodule.homOfLe_apply
- removed Finset.sym2_eq_empty
- removed Finset.sym2_univ
- removed LieSubmodule.homOfLe
- removed LieSubalgebra.homOfLe_apply
- removed Finset.sym2_nonempty
- removed Sym2.card_image_offDiag
- removed Finset.sym2_singleton
- removed CochainComplex.shiftFunctor_map_f
- removed Sym2.card
- removed Finset.isDiag_mk'_of_mem_diag
- removed Finset.sym2_mono
- removed Submodule.ker_ofLe
- removed LieSubalgebra.homOfLe_injective
! type changed for Cardinal.mk_finsupp_lift_of_fintype
! type changed for Basis.coe_mkFinConsOfLE
! type changed for LieSubalgebra.coe_ofLe
! type changed for IntermediateField.equivOfEq_trans
! type changed for LieSubalgebra.equivOfLe_apply
! type changed for LinearMap.quotientInfEquivSupQuotient_apply_mk
! renamed Finset.isDiag_mk'_of_mem_diag → Finset.isDiag_mk_of_mem_diag
! renamed Finset.not_isDiag_mk'_of_mem_offDiag → Finset.not_isDiag_mk_of_mem_offDiag
! proof changed for LieAlgebra.abelian_radical_iff_solvable_is_abelian
! proof changed for ModularGroup.exists_eq_T_zpow_of_c_eq_zero
! proof changed for Cardinal.mk_finsupp_lift_of_infinite'
! proof changed for LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer
! proof changed for CochainComplex.HomComplex.δ_ofHom
! proof changed for Submodule.basis_of_pid_aux
! proof changed for LinearPMap.inf
! proof changed for CategoryTheory.Adjunction.isEquivalenceCreatesColimits
! proof changed for IntermediateField.adjoin_subset_adjoin_iff
! proof changed for LinearPMap.instSub
! proof changed for CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi
! proof changed for Submodule.rank_sup_add_rank_inf_eq
! proof changed for LinearPMap.instAdd
! proof changed for CategoryTheory.GrothendieckTopology.instMonoSheafTypeTypesInstCategorySheafImageSheafImageSheafι
! proof changed for CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono
! proof changed for ClassGroup.exists_mem_finsetApprox
! proof changed for Linarith.strengthenStrictInt
! proof changed for SymOptionSuccEquiv.encode_decode
! proof changed for IntermediateField.biSup_adjoin_simple
! proof changed for CochainComplex.HomComplex.Cochain.zero_comp
! proof changed for padicNorm.int_eq_one_iff
! proof changed for AlgebraicGeometry.IsOpenImmersion.mono
! proof changed for CochainComplex.HomComplex.δ_v
! proof changed for CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
! proof changed for IntermediateField.adjoin_finset_isCompactElement
! proof changed for IntermediateField.normal_iff_normalClosure_eq
! proof changed for Profinite.instFinitaryExtensiveProfiniteCategory
! proof changed for SymOptionSuccEquiv.decode_encode
! proof changed for Stonean.instPreservesPullbacksOfInclusionsStoneanInstLargeCategoryStoneanCompHausCategoryToCompHausHasColimitsOfShape_discreteHasFiniteCoproductsWalkingPairOf_fintypeFintypeWalkingPair
! proof changed for CategoryTheory.Adjunction.isEquivalenceCreatesLimits
! proof changed for CategoryTheory.coyonedaFunctorReflectsLimits
! proof changed for RieszExtension.exists_top
! proof changed for CategoryTheory.IsVanKampenColimit.mapCocone_iff
! proof changed for rank_le_of_submodule
! proof changed for IntermediateField.isSplittingField_iSup
! proof changed for CategoryTheory.yonedaFunctorReflectsLimits
! proof changed for LinearMap.comap_leq_ker_subToSupQuotient
! proof changed for Sym.instSubsingletonSym
! proof changed for CochainComplex.HomComplex.Cochain.comp_zero
! proof changed for Finset.sym_inter
! proof changed for Finset.sym_nonempty
! proof changed for CochainComplex.HomComplex.Cochain.comp_sub
! proof changed for Mathlib.Tactic.Abel.abelNFTarget
! proof changed for CochainComplex.HomComplex.Cochain.map_comp
! proof changed for IntermediateField.exists_finset_of_mem_iSup
! proof changed for CochainComplex.HomComplex.Cochain.comp_add
! proof changed for SimplexCategory.epi_iff_surjective
! proof changed for LieSubalgebra.mem_ofLe
! proof changed for LieSubalgebra.ofLe
! proof changed for Mathlib.Tactic.Abel.abelNFLocalDecl
! proof changed for CochainComplex.HomComplex.Cochain.comp_assoc_of_second_degree_eq_neg_third_degree
! proof changed for LinearPMap.domRestrict_apply
! proof changed for CochainComplex.shiftFunctor
! proof changed for CochainComplex.HomComplex.Cochain.neg_comp
! proof changed for LinearPMap.domRestrict
! proof changed for IntermediateField.adjoin_simple_isCompactElement
! proof changed for Stonean.instFinitaryExtensiveStoneanInstLargeCategoryStonean
! proof changed for Basis.card_le_card_of_le
! proof changed for CochainComplex.HomComplex.Cochain.comp_assoc
! proof changed for SimplexCategory.mono_iff_injective
! proof changed for CochainComplex.HomComplex.Cochain.add_comp
! proof changed for CochainComplex.HomComplex.Cochain.comp_smul
! proof changed for LieAlgebra.le_solvable_ideal_solvable
! proof changed for IsIntegralClosure.isNoetherian
! proof changed for CochainComplex.HomComplex.Cochain.smul_comp
! proof changed for CochainComplex.HomComplex.Cochain.comp_assoc_of_third_is_zero_cochain
! proof changed for CochainComplex.HomComplex.δ_shape
! proof changed for IntermediateField.adjoin_simple_eq_bot_iff
! proof changed for CochainComplex.HomComplex.δ_zero_cochain_v
! proof changed for LinearMap.subToSupQuotient
! proof changed for isArtinian_of_le
! proof changed for LinearMap.quotientInfEquivSupQuotient_surjective
! proof changed for RingOfIntegers.isUnit_norm
! proof changed for PythagoreanTriple.coprime_classification'
! proof changed for CompHaus.instFinitaryExtensiveCompHausCategory
! proof changed for AlgHom.fieldRange_of_normal
! proof changed for CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain
! proof changed for LinearMap.quotientInfEquivSupQuotient_symm_apply_left
! proof changed for Lean.Expr.intLit!
! proof changed for LinearMap.quotientInfEquivSupQuotient_injective
! proof changed for Lean.MVarId.liftReflToEq
! proof changed for CochainComplex.HomComplex.Cochain.sub_comp
! proof changed for CochainComplex.HomComplex.δ_δ
! proof changed for IntermediateField.normal_iff_forall_map_eq
! proof changed for CochainComplex.HomComplex.δ_comp
! proof changed for Linarith.mkNonstrictIntProof
! proof changed for Lean.Expr.natLit!
! proof changed for AddGroupCat.epi_iff_surjective
! proof changed for AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMonoSheafedSpaceInstCategorySheafedSpace
! proof changed for CochainComplex.HomComplex.Cochain.comp_neg
! proof changed for ModularGroup.g_eq_of_c_eq_one
! proof changed for IntermediateField.isSplittingField_iff
! proof changed for Multiset.count_eq_one_of_mem
! proof changed for LieSubalgebra.equivOfLe
287 differences, some not shown
total 23.6s
```
