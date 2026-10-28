import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD

/-! # Singular Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SingularPeriods.IntegralSingularPeriods

noncomputable section

/-! Actual degree-one singular periods with arbitrary integral-module
coefficients, including the integral and rational-mod-integral groups. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V)

/-- Normalize the primitive of the actual pulled-back singular cocycle. -/
def primitive : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 →ₗ[R]
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).X 0 :=
  (HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitiveLinearMap M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0).comp
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)) 1)

/-- The point function of the normalized zero-cochain primitive. -/
def primitiveValue : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 →ₗ[R] (V → M) :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom.hom.comp (primitive M Λ)

theorem primitive_d (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (primitive M Λ c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 c.1 :=
  HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitive_d M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0 _

@[simp]
theorem primitiveValue_zero (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    primitiveValue M Λ c 0 = 0 := HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.normalizedPrimitive_at_basepoint M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0 _

/-- Pullback commutes with the degree-zero singular coboundary. -/
theorem zeroPullback_d {X Y : TopCat.{0}} (f : X ⟶ Y)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y).X 0) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f 0 b) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f 1 ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y).d 0 1 b) := by
  have h := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).comm 0 1) b
  simpa only [ConcreteCategory.comp_apply] using h

/-- Deck translation leaves the coboundary of the normalized primitive fixed. -/
theorem translated_primitive_d (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ℓ : Λ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.translation Λ ℓ)).f 0 (primitive M Λ c)) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (primitive M Λ c) := by
  rw [zeroPullback_d M, primitive_d M]
  change (((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)) ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.translation Λ ℓ)).f 1) c.1 = _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.translation_projection]

/-- The change of the primitive under a deck translation is exactly its
value on that lattice vector. -/
theorem primitiveValue_translate (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ℓ : Λ) (v : V) :
    primitiveValue M Λ c (v + (ℓ : V)) = primitiveValue M Λ c v + primitiveValue M Λ c ℓ := by
  have h := HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.difference_point_value M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))
    ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.translation Λ ℓ)).f 0 (primitive M Λ c))
    (primitive M Λ c) (translated_primitive_d M Λ c ℓ) 0 v
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback] at h
  change primitiveValue M Λ c (0 + (ℓ : V)) - primitiveValue M Λ c 0 =
    primitiveValue M Λ c (v + (ℓ : V)) - primitiveValue M Λ c v at h
  rw [zero_add, primitiveValue_zero M, sub_zero] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- Periods of an actual singular one-cocycle form an additive character
on the actual lattice subgroup. -/
def periodHom (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) : Λ →+ M where
  toFun ℓ := primitiveValue M Λ c ℓ
  map_zero' := primitiveValue_zero M Λ c
  map_add' ℓ μ := primitiveValue_translate M Λ c μ ℓ

/-- The additive lattice character depends linearly on the singular cocycle. -/
def periodLinearMap : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 →ₗ[R] (Λ →+ M) where
  toFun := periodHom M Λ
  map_add' c d := by
    ext ℓ
    exact congrFun ((primitiveValue M Λ).map_add c d) ℓ
  map_smul' r c := by
    ext ℓ
    exact congrFun ((primitiveValue M Λ).map_smul r c) ℓ

/-- Coboundaries have zero periods: their pulled-back primitive differs
from the pulled-back zero-cochain by a constant. -/
theorem periodHom_of_boundary (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 0 1 b = c.1) : periodHom M Λ c = 0 := by
  have hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (primitive M Λ c) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 0 b) := by
    rw [zeroPullback_d M, hb]
    exact primitive_d M Λ c
  ext ℓ
  change primitiveValue M Λ c ℓ = 0
  have h := HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.difference_point_value M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) (primitive M Λ c)
    ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 0 b) hd ℓ 0
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback] at h
  change primitiveValue M Λ c ℓ - (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).hom b
      (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ ℓ) = primitiveValue M Λ c 0 -
        (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).hom b (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ 0) at h
  have hq : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ ℓ = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ 0 := by
    change (QuotientAddGroup.mk (ℓ : V) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk 0
    rw [(QuotientAddGroup.eq_zero_iff (ℓ : V)).mpr ℓ.property]
    rfl
  rw [hq, primitiveValue_zero M] at h
  exact sub_left_inj.mp h

/-- A point function on the quotient, evaluated using any chosen lift. -/
def descendedPrimitiveValue (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (V ⧸ Λ.toAddSubgroup) → M := fun q =>
  primitiveValue M Λ c (QuotientAddGroup.mk_surjective q).choose

/-- Zero periods remove the dependence on the chosen representative. -/
theorem descendedPrimitiveValue_mk (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1)
    (hc : periodHom M Λ c = 0) (v : V) :
    descendedPrimitiveValue M Λ c (QuotientAddGroup.mk v) = primitiveValue M Λ c v := by
  let w : V := (QuotientAddGroup.mk_surjective
    (QuotientAddGroup.mk v : V ⧸ Λ.toAddSubgroup)).choose
  have hq : (QuotientAddGroup.mk w : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk v :=
    (QuotientAddGroup.mk_surjective (QuotientAddGroup.mk v : V ⧸ Λ.toAddSubgroup)).choose_spec
  have hl : w - v ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hq
  have hp := congrArg (fun f : Λ →+ M => f ⟨w - v, hl⟩) hc
  change primitiveValue M Λ c (w - v) = 0 at hp
  have h := primitiveValue_translate M Λ c ⟨w - v, hl⟩ v
  have he : v + (w - v) = w := by abel
  change primitiveValue M Λ c w = primitiveValue M Λ c v
  simpa only [he, hp, add_zero] using h

/-- A cocycle with zero lattice periods is an actual singular coboundary. -/
theorem boundary_of_periodHom_eq_zero [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (hc : periodHom M Λ c = 0) :
    ∃ b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).X 0,
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 0 1 b = c.1 := by
  let b := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).inv (descendedPrimitiveValue M Λ c)
  have hb : (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 0 b = primitive M Λ c := by
    apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).toLinearEquiv.injective
    change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 0 b) =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (primitive M Λ c)
    ext v
    rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback]
    change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).hom
        ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).inv
          (descendedPrimitiveValue M Λ c)) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ v) = primitiveValue M Λ c v
    rw [Iso.inv_hom_id_apply]
    exact descendedPrimitiveValue_mk M Λ c hc v
  have hcover : IsCoveringMap (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) :=
    (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap
  refine ⟨b, ?_⟩
  apply HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) hcover
    QuotientAddGroup.mk_surjective M 1
  rw [← zeroPullback_d M, hb, primitive_d M]

/-- Vanishing of periods detects the zero class in genuine singular H¹. -/
theorem periodHom_eq_zero_iff [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    periodHom M Λ c = 0 ↔ AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c = 0 := by
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := boundary_of_periodHom_eq_zero M Λ c hc
    have h := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 0 c 0).mpr
      ⟨b, by simpa only [Submodule.coe_zero, sub_zero] using hb⟩
    simpa only [map_zero] using h
  · intro hc
    have h : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 0 := by
      simpa only [map_zero] using hc
    obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 0 c 0).mp h
    exact periodHom_of_boundary M Λ c b (by simpa only [Submodule.coe_zero, sub_zero] using hb)

/-- The period map descends to the project's actual singular H¹ object. -/
def cohomologyPeriod [DiscreteTopology Λ] :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 →ₗ[R] (Λ →+ M) :=
  ((AlgebraicTopology.Cohomology.Singular.Representatives.singularBoundaries M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1).liftQ (periodLinearMap M Λ) (by
    intro c hc
    exact (periodHom_eq_zero_iff M Λ c).mpr
      ((AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_zero_iff M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c).mpr hc))).comp
    (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1).toLinearEquiv.toLinearMap

@[simp]
theorem cohomologyPeriod_class [DiscreteTopology Λ]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    cohomologyPeriod M Λ (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c) = periodHom M Λ c := by
  unfold cohomologyPeriod
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraicTopology.Cohomology.Singular.Representatives.singularClass, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Distinct genuine singular H¹ classes have distinct lattice periods. -/
theorem cohomologyPeriod_injective [DiscreteTopology Λ] :
    Function.Injective (cohomologyPeriod M Λ) := by
  intro a b hab
  have hz : cohomologyPeriod M Λ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 (a - b)
  rw [← hc, cohomologyPeriod_class M] at hz
  have h := (periodHom_eq_zero_iff M Λ c).mp hz
  rw [hc] at h
  exact sub_eq_zero.mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SingularPeriods.IntegralSingularPeriods
