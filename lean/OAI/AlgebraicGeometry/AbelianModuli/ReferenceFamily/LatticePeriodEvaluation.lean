import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Lattice Period Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters

noncomputable section

section

/-!
# ReferenceFamily: singular H¹ and actual rational lattice characters

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
  obtain ⟨F, hF⟩ := SingularPeriodEquiv.SingularPeriodComparison.exists_additive_extension Λ φ
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
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 ≃ₗ[ℚ]
      Module.Dual ℚ (RationalSpan Λ) :=
  (SingularPeriodEquiv.SingularPeriodComparison.cohomologyPeriodEquiv Λ).trans (characterRestrictionEquiv Λ).symm

end

/-! The lattice-dual equivalence evaluates to the actual constructed
singular period character on every integral period. -/

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Module ℚ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ]

theorem singularH1LatticeDualEquiv_lattice (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ell : Λ) :
    singularH1LatticeDualEquiv Λ c (latticeInclusion Λ ell) = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ c ell := by
  have h := (characterRestrictionEquiv (K := ℚ) Λ).apply_symm_apply
    (SingularPeriodEquiv.SingularPeriodComparison.cohomologyPeriodEquiv Λ c)
  exact congrArg (fun a : Λ →+ ℚ => a ell) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters
