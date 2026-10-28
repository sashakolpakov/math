import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Minimal Section Local Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalSectionLocalEquations

noncomputable section

/-! If a fiber has one-dimensional H0 and a normalized section, its
normalized-section functor has exactly H1-many local equations. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)

def minimalFirstRankOne
    (h0 : Module.finrank (IsLocalRing.ResidueField R)
      (LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).f.hom) = 1) :
    R ≃ₗ[R] P.complex.X₁ :=
  LinearEquiv.ofFinrankEq R P.complex.X₁
    ((Module.finrank_self R).trans (P.first_finrank_eq_residue_cycles.trans h0).symm)

theorem minimalSectionFunctional_isUnit
    (e : R ≃ₗ[R] P.complex.X₁) (v : S.X₁ →ₗ[R] R)
    (hsection : ∃ m : IsLocalRing.ResidueField R ⊗[R] S.X₁,
      S.f.hom.baseChange (IsLocalRing.ResidueField R) m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange (IsLocalRing.ResidueField R) v m = 1) :
    IsUnit (MinimalNormalizedSections.minimalSectionFunctional P v (e 1)) := by
  let k := IsLocalRing.ResidueField R
  obtain ⟨m, _, hm⟩ := (MinimalNormalizedSections.normalized_minimal_cycles_iff P k v).mp hsection
  let e' := Normalized.KernelBaseChange.rankOneBaseChange k e
  let v' := Normalized.KernelBaseChange.scalarFunctionalBaseChange k (MinimalNormalizedSections.minimalSectionFunctional P v)
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hz
  have hzero : v' (e' 1) = 0 := by
    change Normalized.KernelBaseChange.scalarFunctionalBaseChange k (MinimalNormalizedSections.minimalSectionFunctional P v)
      (Normalized.KernelBaseChange.rankOneBaseChange k e 1) = 0
    rw [Normalized.KernelBaseChange.rankOneBaseChange_one, Normalized.KernelBaseChange.scalarFunctionalBaseChange_tmul, mul_one]
    exact hz
  have he : v' m = e'.symm m • v' (e' 1) := by
    calc
      v' m = v' (e' (e'.symm m)) := congrArg v' (e'.apply_symm_apply m).symm
      _ = _ := (congrArg v' (Normalized.RankOneKernel.rankOne_apply e' (e'.symm m))).trans
        (map_smul v' (e'.symm m) (e' 1))
  rw [hzero, smul_zero] at he
  exact zero_ne_one (he.symm.trans hm)

include P in
theorem exists_minimal_normalized_equations
    (h0 : Module.finrank (IsLocalRing.ResidueField R)
      (LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).f.hom) = 1)
    (v : S.X₁ →ₗ[R] R)
    (hsection : ∃ m : IsLocalRing.ResidueField R ⊗[R] S.X₁,
      S.f.hom.baseChange (IsLocalRing.ResidueField R) m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange (IsLocalRing.ResidueField R) v m = 1) :
    ∃ n : ℕ, n = Module.finrank (IsLocalRing.ResidueField R)
        (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology ∧
      ∃ r : Fin n → R,
      ∀ (T : Type u) [CommRing T] [Algebra R T],
        (∃ m : T ⊗[R] S.X₁, S.f.hom.baseChange T m = 0 ∧
          Normalized.KernelBaseChange.scalarFunctionalBaseChange T v m = 1) ↔
        Ideal.span (Set.range r) ≤ RingHom.ker (algebraMap R T) := by
  let e := minimalFirstRankOne P h0
  let b := Module.finBasis R P.complex.X₂
  have hu : IsUnit (MinimalNormalizedSections.minimalSectionFunctional P v (e 1)) :=
    minimalSectionFunctional_isUnit P e v hsection
  refine ⟨Module.finrank R P.complex.X₂, P.middle_finrank_eq_residue_cohomology,
    fun i => b.repr (P.complex.f (e 1)) i, ?_⟩
  intro T _ _
  exact MinimalNormalizedSections.normalized_minimal_section_equations P T b e v hu

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalSectionLocalEquations
