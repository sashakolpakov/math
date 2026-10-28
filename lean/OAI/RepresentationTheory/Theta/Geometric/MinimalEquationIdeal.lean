import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
import OAI.RepresentationTheory.Theta.Geometric.RankOneFiberGenerators
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Minimal Equation Ideal -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalEquationIdeal

noncomputable section

/-! The minimal differential defines a proper ideal in the local base.
Its quotient carries the original generator as an actual first cycle. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)
    {I : Type*} (b : Module.Basis I R P.complex.X₂) (e : R ≃ₗ[R] P.complex.X₁)

def minimalEquationIdeal : Ideal R :=
  Ideal.span (Set.range fun i => b.repr (P.complex.f (e 1)) i)

theorem minimalEquationIdeal_le_maximal : minimalEquationIdeal P b e ≤ IsLocalRing.maximalIdeal R := by
  have hz : (1 ⊗ₜ[R] P.complex.f (e 1) : IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) = 0 := by
    change P.complex.f.hom.baseChange (IsLocalRing.ResidueField R) (1 ⊗ₜ[R] e 1) = 0
    rw [P.incoming_residue_zero, LinearMap.zero_apply]
  have hc := (Normalized.KernelBaseChange.tensor_one_eq_zero_iff_coefficients (IsLocalRing.ResidueField R) b _).mp hz
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (IsLocalRing.residue_eq_zero_iff _).mp (hc i)

theorem minimalEquationIdeal_ne_top : minimalEquationIdeal P b e ≠ ⊤ := by
  intro h
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_unique (h ▸ minimalEquationIdeal_le_maximal P b e))

instance minimalEquationQuotient_nontrivial : Nontrivial (R ⧸ minimalEquationIdeal P b e) :=
  Ideal.Quotient.nontrivial_iff.mpr (minimalEquationIdeal_ne_top P b e)

instance minimalEquationQuotient_isLocalRing : IsLocalRing (R ⧸ minimalEquationIdeal P b e) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (minimalEquationIdeal P b e))
    Ideal.Quotient.mk_surjective

theorem minimalEquationIdeal_generator_cycle :
    P.complex.f.hom.baseChange (R ⧸ minimalEquationIdeal P b e) (1 ⊗ₜ[R] e 1) = 0 := by
  change (1 ⊗ₜ[R] P.complex.f (e 1) : (R ⧸ minimalEquationIdeal P b e) ⊗[R] P.complex.X₂) = 0
  apply (Normalized.KernelBaseChange.tensor_one_eq_zero_iff_coefficients (R ⧸ minimalEquationIdeal P b e) b _).mpr
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem minimalEquationIdeal_generators_iff (T : Type u) [CommRing T] [Algebra R T] :
    (∃ m : T ⊗[R] P.complex.X₁, P.complex.f.hom.baseChange T m = 0 ∧
      IsUnit ((Normalized.KernelBaseChange.rankOneBaseChange T e).symm m)) ↔
      minimalEquationIdeal P b e ≤ RingHom.ker (algebraMap R T) :=
  RankOneFiberGenerators.rankOne_generator_cycle_equations T b e P.complex.f.hom

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalEquationIdeal
