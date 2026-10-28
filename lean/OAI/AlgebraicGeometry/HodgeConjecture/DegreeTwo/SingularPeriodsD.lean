import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularCoveringLift
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Covering.Quotient

/-! # Singular Periods D -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods

noncomputable section

/-!
# DegreeTwo: periods of actual singular one-cocycles

Pull a cocycle back to the contractible vector-space covering and take its
unique normalized primitive. Translation by a lattice vector changes that
primitive by a constant, and those constants form an additive period map.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

variable {K : Type} [Field K]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V)

abbrev Coeff := ModuleCat.of ℚ ℚ
abbrev Cover := TopCat.of V
abbrev Base := TopCat.of (V ⧸ Λ.toAddSubgroup)

/-- The genuine lattice covering, as a continuous map. -/
def projection : Cover (V := V) ⟶ Base Λ :=
  TopCat.ofHom ⟨QuotientAddGroup.mk, QuotientAddGroup.continuous_mk⟩

/-- Normalize the primitive of the actual pulled-back singular cocycle. -/
def primitive : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1 →ₗ[K]
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).X 0 :=
  (OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitiveLinearMap (ModuleCat.of K K) (Cover (V := V)) 0).comp
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)) 1)

/-- The point function of the normalized zero-cochain primitive. -/
def primitiveValue : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1 →ₗ[K] (V → K) :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Cover (V := V))).hom.hom.comp (primitive Λ)

theorem primitive_d (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).d 0 1 (primitive Λ c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)).f 1 c.1 :=
  OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitive_d (ModuleCat.of K K) (Cover (V := V)) 0 _

@[simp]
theorem primitiveValue_zero (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) :
    primitiveValue Λ c 0 = 0 := OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitive_at_basepoint (ModuleCat.of K K) (Cover (V := V)) 0 _

/-- Translation by a period on the actual covering vector space. -/
def translation (ℓ : Λ) : Cover (V := V) ⟶ Cover (V := V) :=
  TopCat.ofHom ⟨fun v => v + (ℓ : V), continuous_id.add continuous_const⟩

omit [NormedSpace ℝ V] in
@[simp]
theorem translation_projection (ℓ : Λ) : translation Λ ℓ ≫ projection Λ = projection Λ := by
  apply TopCat.ext
  intro v
  change (QuotientAddGroup.mk (v + (ℓ : V)) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk v
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (ℓ : V)).mpr ℓ.property,
    add_zero]

/-- Pullback commutes with the degree-zero singular coboundary. -/
theorem zeroPullback_d {X Y : TopCat.{0}} (f : X ⟶ Y)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) Y).X 0) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) X).d 0 1 ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) f).f 0 b) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) f).f 1 ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) Y).d 0 1 b) := by
  have h := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) f).comm 0 1) b
  simpa only [ConcreteCategory.comp_apply] using h

/-- Deck translation leaves the coboundary of the normalized primitive fixed. -/
theorem translated_primitive_d (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) (ℓ : Λ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).d 0 1
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (translation Λ ℓ)).f 0 (primitive Λ c)) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).d 0 1 (primitive Λ c) := by
  rw [zeroPullback_d, primitive_d]
  change (((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)) ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (translation Λ ℓ)).f 1) c.1 = _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, translation_projection]

/-- The change of the primitive under a deck translation is exactly its
value on that lattice vector. -/
theorem primitiveValue_translate (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) (ℓ : Λ) (v : V) :
    primitiveValue Λ c (v + (ℓ : V)) = primitiveValue Λ c v + primitiveValue Λ c ℓ := by
  have h := OnePrimitives.Constructions.DegreeOnePrimitives.difference_point_value (ModuleCat.of K K) (Cover (V := V))
    ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (translation Λ ℓ)).f 0 (primitive Λ c))
    (primitive Λ c) (translated_primitive_d Λ c ℓ) 0 v
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback] at h
  change primitiveValue Λ c (0 + (ℓ : V)) - primitiveValue Λ c 0 =
    primitiveValue Λ c (v + (ℓ : V)) - primitiveValue Λ c v at h
  rw [zero_add, primitiveValue_zero, sub_zero] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- Periods of an actual singular one-cocycle form an additive character
on the actual lattice subgroup. -/
def periodHom (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) : Λ →+ K where
  toFun ℓ := primitiveValue Λ c ℓ
  map_zero' := primitiveValue_zero Λ c
  map_add' ℓ μ := primitiveValue_translate Λ c μ ℓ

/-- The additive lattice character depends linearly on the singular cocycle. -/
def periodLinearMap : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1 →ₗ[K] (Λ →+ K) where
  toFun := periodHom Λ
  map_add' c d := by
    ext ℓ
    exact congrFun ((primitiveValue Λ).map_add c d) ℓ
  map_smul' r c := by
    ext ℓ
    exact congrFun ((primitiveValue Λ).map_smul r c) ℓ

/-- Coboundaries have zero periods: their pulled-back primitive differs
from the pulled-back zero-cochain by a constant. -/
theorem periodHom_of_boundary (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Base Λ)).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Base Λ)).d 0 1 b = c.1) : periodHom Λ c = 0 := by
  have hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).d 0 1 (primitive Λ c) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Cover (V := V))).d 0 1
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)).f 0 b) := by
    rw [zeroPullback_d, hb]
    exact primitive_d Λ c
  ext ℓ
  change primitiveValue Λ c ℓ = 0
  have h := OnePrimitives.Constructions.DegreeOnePrimitives.difference_point_value (ModuleCat.of K K) (Cover (V := V)) (primitive Λ c)
    ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)).f 0 b) hd ℓ 0
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback] at h
  change primitiveValue Λ c ℓ - (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Base Λ)).hom b
      (projection Λ ℓ) = primitiveValue Λ c 0 -
        (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Base Λ)).hom b (projection Λ 0) at h
  have hq : projection Λ ℓ = projection Λ 0 := by
    change (QuotientAddGroup.mk (ℓ : V) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk 0
    rw [(QuotientAddGroup.eq_zero_iff (ℓ : V)).mpr ℓ.property]
    rfl
  rw [hq, primitiveValue_zero] at h
  exact sub_left_inj.mp h

/-- A point function on the quotient, evaluated using any chosen lift. -/
def descendedPrimitiveValue (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) :
    (V ⧸ Λ.toAddSubgroup) → K := fun q =>
  primitiveValue Λ c (QuotientAddGroup.mk_surjective q).choose

/-- Zero periods remove the dependence on the chosen representative. -/
theorem descendedPrimitiveValue_mk (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1)
    (hc : periodHom Λ c = 0) (v : V) :
    descendedPrimitiveValue Λ c (QuotientAddGroup.mk v) = primitiveValue Λ c v := by
  let w : V := (QuotientAddGroup.mk_surjective
    (QuotientAddGroup.mk v : V ⧸ Λ.toAddSubgroup)).choose
  have hq : (QuotientAddGroup.mk w : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk v :=
    (QuotientAddGroup.mk_surjective (QuotientAddGroup.mk v : V ⧸ Λ.toAddSubgroup)).choose_spec
  have hl : w - v ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hq
  have hp := congrArg (fun f : Λ →+ K => f ⟨w - v, hl⟩) hc
  change primitiveValue Λ c (w - v) = 0 at hp
  have h := primitiveValue_translate Λ c ⟨w - v, hl⟩ v
  have he : v + (w - v) = w := by abel
  change primitiveValue Λ c w = primitiveValue Λ c v
  simpa only [he, hp, add_zero] using h

/-- A cocycle with zero lattice periods is an actual singular coboundary. -/
theorem boundary_of_periodHom_eq_zero [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) (hc : periodHom Λ c = 0) :
    ∃ b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Base Λ)).X 0,
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Base Λ)).d 0 1 b = c.1 := by
  let b := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Base Λ)).inv (descendedPrimitiveValue Λ c)
  have hb : (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)).f 0 b = primitive Λ c := by
    apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Cover (V := V))).toLinearEquiv.injective
    change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Cover (V := V))).hom
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (projection Λ)).f 0 b) =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Cover (V := V))).hom (primitive Λ c)
    ext v
    rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback]
    change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Base Λ)).hom
        ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (Base Λ)).inv
          (descendedPrimitiveValue Λ c)) (projection Λ v) = primitiveValue Λ c v
    rw [Iso.inv_hom_id_apply]
    exact descendedPrimitiveValue_mk Λ c hc v
  have hcover : IsCoveringMap (projection Λ) :=
    (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap
  refine ⟨b, ?_⟩
  apply SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective (projection Λ) hcover
    QuotientAddGroup.mk_surjective (ModuleCat.of K K) 1
  rw [← zeroPullback_d, hb, primitive_d]

/-- Vanishing of periods detects the zero class in genuine singular H¹. -/
theorem periodHom_eq_zero_iff [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) :
    periodHom Λ c = 0 ↔ AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (Base Λ) 1 c = 0 := by
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := boundary_of_periodHom_eq_zero Λ c hc
    have h := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ (ModuleCat.of K K) (Base Λ) 0 c 0).mpr
      ⟨b, by simpa only [Submodule.coe_zero, sub_zero] using hb⟩
    simpa only [map_zero] using h
  · intro hc
    have h : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (Base Λ) 1 c = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (Base Λ) 1 0 := by
      simpa only [map_zero] using hc
    obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ (ModuleCat.of K K) (Base Λ) 0 c 0).mp h
    exact periodHom_of_boundary Λ c b (by simpa only [Submodule.coe_zero, sub_zero] using hb)

/-- The period map descends to the project's actual singular H¹ object. -/
def cohomologyPeriod [DiscreteTopology Λ] :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of K K) (Base Λ) 1 →ₗ[K] (Λ →+ K) :=
  ((AlgebraicTopology.Cohomology.Singular.Representatives.singularBoundaries (ModuleCat.of K K) (Base Λ) 1).liftQ (periodLinearMap Λ) (by
    intro c hc
    exact (periodHom_eq_zero_iff Λ c).mpr
      ((AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_zero_iff (ModuleCat.of K K) (Base Λ) 1 c).mpr hc))).comp
    (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of K K) (Base Λ)) 1).toLinearEquiv.toLinearMap

@[simp]
theorem cohomologyPeriod_class [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (Base Λ) 1) :
    cohomologyPeriod Λ (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (Base Λ) 1 c) = periodHom Λ c := by
  unfold cohomologyPeriod
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraicTopology.Cohomology.Singular.Representatives.singularClass, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Distinct genuine singular H¹ classes have distinct lattice periods. -/
theorem cohomologyPeriod_injective [DiscreteTopology Λ] :
    Function.Injective (cohomologyPeriod (K := K) Λ) := by
  intro a b hab
  have hz : cohomologyPeriod Λ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of K K) (Base Λ) 1 (a - b)
  rw [← hc, cohomologyPeriod_class] at hz
  have h := (periodHom_eq_zero_iff Λ c).mp hz
  rw [hc] at h
  exact sub_eq_zero.mp h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods
