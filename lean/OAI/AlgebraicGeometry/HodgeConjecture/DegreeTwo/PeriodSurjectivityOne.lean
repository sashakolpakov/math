import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD
import Mathlib.Algebra.Category.Grp.Injective

/-! # Period Surjectivity One -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodSurjectivityOne.Constructions.PeriodSurjectivity

noncomputable section

/-!
# DegreeTwo: realizing lattice characters by singular cocycles

A characteristic-zero field-valued lattice character extends additively to the covering vector space
because the additive group of the coefficient field is injective. Its zero-cochain
coboundary is unchanged when a simplex lift is translated by a lattice
element, so that coboundary descends to an actual singular one-cocycle.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial _root_.Topology

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

variable {K : Type} [Field K]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ]

omit [NormedSpace ℝ V] [DiscreteTopology Λ] in
/-- Any field-valued character on the lattice has an additive extension to V. -/
theorem exists_additive_extension [CharZero K] (φ : Λ →+ K) :
    ∃ F : V →+ K, ∀ ℓ : Λ, F ℓ = φ ℓ := by
  let : Module.Injective ℤ K := (Module.Baer.of_divisible K).injective
  obtain ⟨F, hF⟩ := Module.Injective.out Λ.subtype Λ.subtype_injective φ.toIntLinearMap
  exact ⟨F.toAddMonoidHom, hF⟩

omit [NormedSpace ℝ V] in
/-- Two continuous lifts over a connected parameter space differ by a
single lattice translation. -/
theorem lift_difference_constant {S : Type} [TopologicalSpace S] [PreconnectedSpace S]
    (a b : C(S, V))
    (hab : ∀ s, (QuotientAddGroup.mk (a s) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk (b s))
    (s t : S) : a s - b s = a t - b t := by
  let d : S → Λ := fun z => ⟨a z - b z, QuotientAddGroup.eq_iff_sub_mem.mp (hab z)⟩
  have hd : Continuous d := (a.continuous.sub b.continuous).subtype_mk _
  have hl : IsLocallyConstant d := (IsLocallyConstant.iff_continuous d).mpr hd
  exact congrArg Subtype.val (hl.apply_eq_of_preconnectedSpace s t)

/-- An additive function is used as a genuine singular zero-cochain. -/
def additiveZeroCochain (F : V →+ K) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)

omit [NormedSpace ℝ V] in
@[simp]
theorem additiveZeroCochain_value (F : V →+ K) (v : V) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain F) v = F v := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)) v = F v
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- The coboundary of an additive point function is its endpoint difference. -/
theorem additiveCoboundary_apply (F : V →+ K)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) s =
      F (TopCat.toSSetObj₁Equiv s 1) - F (TopCat.toSSetObj₁Equiv s 0) := by
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply, additiveZeroCochain_value, additiveZeroCochain_value,
    TopCat.toSSetObj₁Equiv_apply_one, TopCat.toSSetObj₁Equiv_apply_zero]

omit [NormedSpace ℝ V] in
/-- Endpoint differences of an additive function are independent of the
chosen lift of a singular edge. -/
theorem additiveCoboundary_lift_invariant (F : V →+ K)
    (s t : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1)
    (hst : (TopCat.toSSet.map (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) s =
      (TopCat.toSSet.map (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) t) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) t := by
  let a := TopCat.toSSetObj₁Equiv s
  let b := TopCat.toSSetObj₁Equiv t
  let : PreconnectedSpace TopCat.I := by
    constructor
    rw [← TopCat.I.homeomorph.symm.surjective.range_eq]
    exact isPreconnected_range TopCat.I.homeomorph.symm.continuous
  have hab (z : TopCat.I) :
      (QuotientAddGroup.mk (a z) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk (b z) := by
    exact congrArg (fun u => TopCat.toSSetObj₁Equiv u z) hst
  have hd := lift_difference_constant Λ a.hom b.hom hab 1 0
  have h := congrArg F hd
  rw [map_sub, map_sub] at h
  rw [additiveCoboundary_apply, additiveCoboundary_apply]
  change F (a 1) - F (a 0) = F (b 1) - F (b 0)
  exact sub_eq_sub_iff_sub_eq_sub.mp h

omit [NormedSpace ℝ V] in
theorem projection_covering : IsCoveringMap (SingularPeriodsD.Constructions.SingularPeriods.projection Λ) :=
  (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap

/-- Choose an actual lift of each singular edge. -/
def edgeLift (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1 :=
  (SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective (SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective 1 s).choose

omit [NormedSpace ℝ V] in
theorem edgeLift_spec (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (TopCat.toSSet.map (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) (edgeLift Λ s) = s :=
  (SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective (SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective 1 s).choose_spec

/-- Descend the coboundary of the additive extension by lifting edges. -/
def descendedOneCochain (F : V →+ K) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of K K) 1).inv
    (fun s => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) (edgeLift Λ s))

omit [NormedSpace ℝ V] in
theorem descendedOneCochain_apply (F : V →+ K) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of K K) 1).hom
        (descendedOneCochain Λ F) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) (edgeLift Λ s) := by
  unfold descendedOneCochain
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- Pulling back the descended cochain recovers the actual coboundary of F. -/
theorem descendedOneCochain_pullback (F : V →+ K) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain Λ F) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of K K) (TopCat.toSSet.map (SingularPeriodsD.Constructions.SingularPeriods.projection Λ))).f 1 (descendedOneCochain Λ F)) = _
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, descendedOneCochain_apply]
  exact additiveCoboundary_lift_invariant Λ F _ s (edgeLift_spec Λ _)

omit [NormedSpace ℝ V] in
/-- The descended cochain is closed, as can be tested after pulling back
to the covering, where it is literally a coboundary. -/
theorem descendedOneCochain_closed (F : V →+ K) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain Λ F) = 0 := by
  apply SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective (SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective (ModuleCat.of K K) 2
  rw [map_zero]
  have hcomm := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).comm 1 2)
    (descendedOneCochain Λ F)
  have hd := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d_comp_d 0 1 2) (additiveZeroCochain F)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 1 2
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain Λ F)) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 2
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain Λ F)) at hcomm
  rw [← hcomm, descendedOneCochain_pullback]
  exact hd

/-- The actual singular cocycle obtained from an additive extension. -/
def descendedCocycle (F : V →+ K) : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 :=
  ⟨descendedOneCochain Λ F,
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr (descendedOneCochain_closed Λ F)⟩

/-- The normalized primitive of this cocycle is the original additive
function, interpreted as an actual singular zero-cochain. -/
theorem primitive_descendedCocycle (F : V →+ K) :
    SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (descendedCocycle Λ F) = additiveZeroCochain F := by
  apply OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [SingularPeriodsD.Constructions.SingularPeriods.primitive_d]
    exact descendedOneCochain_pullback Λ F
  · change SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (descendedCocycle Λ F) 0 =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain F) 0
    rw [SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero, additiveZeroCochain_value, map_zero]

/-- The constructed cocycle realizes precisely the prescribed periods. -/
theorem periodHom_descendedCocycle (F : V →+ K) (ℓ : Λ) :
    SingularPeriodsD.Constructions.SingularPeriods.periodHom Λ (descendedCocycle Λ F) ℓ = F ℓ := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
    (SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (descendedCocycle Λ F)) ℓ = F ℓ
  rw [primitive_descendedCocycle, additiveZeroCochain_value]

variable [CharZero K]

/-- Every additive field-valued lattice character occurs as the period map
of a genuine singular H¹ class. -/
theorem cohomologyPeriod_surjective : Function.Surjective (SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (K := K) Λ) := by
  intro φ
  obtain ⟨F, hF⟩ := exists_additive_extension Λ φ
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 (descendedCocycle Λ F), ?_⟩
  rw [SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  ext ℓ
  exact (periodHom_descendedCocycle Λ F ℓ).trans (hF ℓ)

/-- The actual singular H¹ of a lattice quotient is canonically its
space of additive field-valued lattice characters. -/
def cohomologyPeriodEquiv : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 ≃ₗ[K] (Λ →+ K) :=
  LinearEquiv.ofBijective (SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ)
    ⟨SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_injective Λ, cohomologyPeriod_surjective Λ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodSurjectivityOne.Constructions.PeriodSurjectivity
