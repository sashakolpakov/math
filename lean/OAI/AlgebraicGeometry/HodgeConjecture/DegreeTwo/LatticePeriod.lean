import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodSurjectivityOne
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Lattice Period -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual

/-!
# DegreeTwo: singular H¹ and the rational lattice dual

Restriction to the lattice identifies the dual of its rational span with
additive rational lattice characters. Together with the singular period
equivalence this supplies the rational H¹ model used by BettiLattice.
-/

variable {K : Type} [Field K] [CharZero K]

variable {V : Type} [NormedAddCommGroup V] [Module ℚ V] (Λ : Submodule ℤ V)

abbrev RationalSpan := Submodule.span ℚ (Λ : Set V)

/-- The actual lattice embeds in its rational linear span. -/
def latticeInclusion : Λ →+ RationalSpan Λ where
  toFun ℓ := ⟨ℓ, Submodule.subset_span ℓ.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restrict a rational covector to the actual lattice. -/
def characterRestriction : (RationalSpan Λ →ₗ[ℚ] K) →ₗ[K] (Λ →+ K) where
  toFun f := f.toAddMonoidHom.comp (latticeInclusion Λ)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- A rational covector is determined by its values on the spanning lattice. -/
theorem characterRestriction_injective : Function.Injective (characterRestriction (K := K) Λ) := by
  intro f g h
  ext v
  rcases v with ⟨v, hv⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact DFunLike.congr_fun h ⟨x, hx⟩
  | zero =>
    change f 0 = g 0
    simp
  | add x y hx hy hfx hfy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, hfx, hfy]
  | smul r x hx hfx =>
    change f (r • (⟨x, hx⟩ : RationalSpan Λ)) = g (r • (⟨x, hx⟩ : RationalSpan Λ))
    rw [map_smul, map_smul, hfx]

/-- An additive rational character extends rationally linearly to the span. -/
theorem characterRestriction_surjective : Function.Surjective (characterRestriction (K := K) Λ) := by
  intro φ
  obtain ⟨F, hF⟩ := PeriodSurjectivityOne.Constructions.PeriodSurjectivity.exists_additive_extension Λ φ
  refine ⟨F.toRatLinearMap.domRestrict (RationalSpan Λ), ?_⟩
  ext ℓ
  exact hF ℓ

/-- The rational lattice dual and additive lattice characters are canonically
the same vector space. -/
def characterRestrictionEquiv : (RationalSpan Λ →ₗ[ℚ] K) ≃ₗ[K] (Λ →+ K) :=
  LinearEquiv.ofBijective (characterRestriction Λ)
    ⟨characterRestriction_injective Λ, characterRestriction_surjective Λ⟩

variable [NormedSpace ℝ V] [DiscreteTopology Λ]

/-- The project's actual singular H¹ is canonically the BettiLattice lattice dual. -/
def singularH1LatticeDualEquiv :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology SingularPeriodsD.Constructions.SingularPeriods.Coeff (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 ≃ₗ[ℚ]
      Module.Dual ℚ (RationalSpan Λ) :=
  (PeriodSurjectivityOne.Constructions.PeriodSurjectivity.cohomologyPeriodEquiv Λ).trans (characterRestrictionEquiv Λ).symm

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual

namespace AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.PeriodNaturality

/-!
# DegreeTwo: naturality of the genuine singular period comparison

For a commuting diagram of pointed covering maps, the normalized primitive
of a pulled-back cocycle is the pullback of its normalized primitive.
Therefore the period comparison respects actual singular pullback.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

variable {K : Type} [Field K]

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Λ : Submodule ℤ V) (Γ : Submodule ℤ W)
  (f : SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V) ⟶ SingularPeriodsD.Constructions.SingularPeriods.Cover (V := W)) (g : SingularPeriodsD.Constructions.SingularPeriods.Base Λ ⟶ SingularPeriodsD.Constructions.SingularPeriods.Base Γ)
  (hsquare : f ≫ SingularPeriodsD.Constructions.SingularPeriods.projection Γ = SingularPeriodsD.Constructions.SingularPeriods.projection Λ ≫ g) (hf₀ : f 0 = 0)

include hsquare hf₀

/-- Pullback commutes with the uniquely normalized primitive. -/
theorem primitive_naturality (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Γ) 1) :
    SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) f).f 0 (SingularPeriodsD.Constructions.SingularPeriods.primitive Γ c) := by
  apply OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [SingularPeriodsD.Constructions.SingularPeriods.primitive_d, SingularPeriodsD.Constructions.SingularPeriods.zeroPullback_d, SingularPeriodsD.Constructions.SingularPeriods.primitive_d]
    change (((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1) c.1 =
      (((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.projection Γ)) ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) f).f 1) c.1
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, hsquare]
  · rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback]
    change SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c) 0 =
      SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Γ c (f 0)
    rw [hf₀, SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero, SingularPeriodsD.Constructions.SingularPeriods.primitiveValue_zero]

/-- The naturality formula holds at each point of the covering vector space. -/
theorem primitiveValue_naturality (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Γ) 1) (v : V) :
    SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c) v =
      SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Γ c (f v) := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
      (SingularPeriodsD.Constructions.SingularPeriods.primitive Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c)) v = _
  rw [primitive_naturality Λ Γ f g hsquare hf₀, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback]
  rfl

/-- The period map intertwines actual singular pullback with the induced
map on lattice vectors in a commuting pointed covering diagram. -/
theorem cohomologyPeriod_naturality [DiscreteTopology Λ] [DiscreteTopology Γ]
    (u : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Γ) 1) (ℓ : Λ) (k : Γ) (hk : (k : W) = f ℓ) :
    SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of K K) g 1 u) ℓ =
      SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Γ u k := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Γ) 1 u
  have hn := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of K K) g 1 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Γ) 1 c) =
    AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of K K) (SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c) at hn
  rw [hn, SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class, SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  change SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of K K) g) 1 c) ℓ =
    SingularPeriodsD.Constructions.SingularPeriods.primitiveValue Γ c k
  rw [primitiveValue_naturality Λ Γ f g hsquare hf₀, hk]

end AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.PeriodNaturality

end

end OAI
