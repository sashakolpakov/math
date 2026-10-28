import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD
import Mathlib.Algebra.Category.Grp.Injective

/-! # Singular Period Equiv -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv.SingularPeriodComparison

/-!
# ReferenceFamily: realizing lattice characters by singular cocycles

This owned specialization uses the DegreeTwo singular-period primitives. Its
proofs keep the ambient real scalar structure out of the purely topological
pullback identity, so the strict checker needs no option changes.

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
def additiveZeroCochain (F : V →+ K) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)

omit [NormedSpace ℝ V] in
@[simp]
theorem additiveZeroCochain_value (F : V →+ K) (v : V) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain F) v = F v := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)) v = F v
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- The coboundary of an additive point function is its endpoint difference. -/
theorem additiveCoboundary_apply (F : V →+ K)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) s =
      F (TopCat.toSSetObj₁Equiv s 1) - F (TopCat.toSSetObj₁Equiv s 0) := by
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply, additiveZeroCochain_value, additiveZeroCochain_value,
    TopCat.toSSetObj₁Equiv_apply_one, TopCat.toSSetObj₁Equiv_apply_zero]

omit [NormedSpace ℝ V] in
/-- Endpoint differences of an additive function are independent of the
chosen lift of a singular edge. -/
theorem additiveCoboundary_lift_invariant (F : V →+ K)
    (s t : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1)
    (hst : (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) s =
      (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) t) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) t := by
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
theorem projection_covering : IsCoveringMap (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) :=
  (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap

/-- Choose an actual lift of each singular edge. -/
def edgeLift (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1 :=
  (HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective 1 s).choose

omit [NormedSpace ℝ V] in
theorem edgeLift_spec (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) (edgeLift Λ s) = s :=
  (HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective 1 s).choose_spec

/-- Descend the coboundary of the additive extension by lifting edges. -/
def descendedOneCochain (F : V →+ K) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of K K) 1).inv
    (fun s => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) (edgeLift Λ s))

omit [NormedSpace ℝ V] in
theorem descendedOneCochain_apply (F : V →+ K) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of K K) 1).hom
        (descendedOneCochain Λ F) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F)) (edgeLift Λ s) := by
  unfold descendedOneCochain
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- Pulling back the descended cochain recovers the actual coboundary of F. -/
theorem descendedOneCochain_pullback (F : V →+ K) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain Λ F) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain F) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) (ModuleCat.of K K) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of K K) (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ))).f 1 (descendedOneCochain Λ F)) = _
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, descendedOneCochain_apply]
  exact additiveCoboundary_lift_invariant Λ F _ s (edgeLift_spec Λ _)

omit [NormedSpace ℝ V] in
/-- The descended cochain is closed, as can be tested after pulling back
to the covering, where it is literally a coboundary. -/
theorem descendedOneCochain_closed (F : V →+ K) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain Λ F) = 0 := by
  apply HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (projection_covering Λ)
    QuotientAddGroup.mk_surjective (ModuleCat.of K K) 2
  rw [map_zero]
  have hcomm := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).comm 1 2)
    (descendedOneCochain Λ F)
  have hd := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d_comp_d 0 1 2) (additiveZeroCochain F)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 1 2
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain Λ F)) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 2
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain Λ F)) at hcomm
  rw [← hcomm, descendedOneCochain_pullback]
  exact hd

/-- The actual singular cocycle obtained from an additive extension. -/
def descendedCocycle (F : V →+ K) : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 :=
  ⟨descendedOneCochain Λ F,
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr (descendedOneCochain_closed Λ F)⟩

/-- The normalized primitive of this cocycle is the original additive
function, interpreted as an actual singular zero-cochain. -/
theorem primitive_descendedCocycle (F : V →+ K) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (descendedCocycle Λ F) = additiveZeroCochain F := by
  apply HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive_d]
    exact descendedOneCochain_pullback Λ F
  · change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (descendedCocycle Λ F) 0 =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain F) 0
    rw [HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero, additiveZeroCochain_value, map_zero]

/-- The constructed cocycle realizes precisely the prescribed periods. -/
theorem periodHom_descendedCocycle (F : V →+ K) (ℓ : Λ) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.periodHom Λ (descendedCocycle Λ F) ℓ = F ℓ := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
    (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (descendedCocycle Λ F)) ℓ = F ℓ
  rw [primitive_descendedCocycle, additiveZeroCochain_value]

variable [CharZero K]

/-- Every additive field-valued lattice character occurs as the period map
of a genuine singular H¹ class. -/
theorem cohomologyPeriod_surjective : Function.Surjective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (K := K) Λ) := by
  intro φ
  obtain ⟨F, hF⟩ := exists_additive_extension Λ φ
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 (descendedCocycle Λ F), ?_⟩
  rw [HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  ext ℓ
  exact (periodHom_descendedCocycle Λ F ℓ).trans (hF ℓ)

/-- The actual singular H¹ of a lattice quotient is canonically its
space of additive field-valued lattice characters. -/
def cohomologyPeriodEquiv : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of K K) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 ≃ₗ[K] (Λ →+ K) :=
  LinearEquiv.ofBijective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ)
    ⟨HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_injective Λ, cohomologyPeriod_surjective Λ⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv.SingularPeriodComparison

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv

/-! The constructed singular period characters are natural for actual
maps of lattice coverings. Normalized primitives prove this directly,
without imposing a new period or homology comparison hypothesis. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Λ : Submodule ℤ V) (Μ : Submodule ℤ W)
    (f : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V) ⟶ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := W)) (g : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ ⟶ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Μ)
    (h : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ ≫ g = f ≫ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Μ) (h0 : f 0 = 0)

include h h0

theorem periodPrimitive_pullback (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Μ) 1) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff g) 1 c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff f).f 0 (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive Μ c) := by
  apply HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive_d, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.zeroPullback_d, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitive_d]
    have he := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) g).symm.trans
      ((congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff) h).trans (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Μ)))
    exact ConcreteCategory.congr_hom (congrArg (fun a => a.f 1) he) c.val
  · rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback]
    change HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff g) 1 c) 0 = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Μ c (f 0)
    rw [h0, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero]

theorem periodPrimitiveValue_pullback (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Μ) 1) (v : V) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff g) 1 c) v = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Μ c (f v) := by
  have he := congrArg (fun a => (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom a v)
    (periodPrimitive_pullback Λ Μ f g h h0 c)
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback] at he
  exact he

theorem cohomologyPeriod_pullback [DiscreteTopology Λ] [DiscreteTopology Μ]
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Μ) 1) (ell : Λ) (mu : Μ) (hm : f ell.val = mu.val) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff g 1 c) ell = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Μ c mu := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Μ) 1 c
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  exact (periodPrimitiveValue_pullback Λ Μ f g h h0 c ell.val).trans
    (congrArg (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Μ c) hm)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv

end

end OAI
