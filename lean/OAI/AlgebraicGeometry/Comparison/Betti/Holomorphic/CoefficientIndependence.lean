import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenDomainSheaf

/-! # Coefficient Independence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientIndependence

noncomputable section

section

/-! Pointwise independent actual holomorphic forms give actual local differential-module bases. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {U V : Opens E}

def openFormHolomorphicSectionFunctionEquiv (U : Opens E) (n : ℕ) :
    DeRhamComplex.forms E U n ≃ₗ[FunctionPure.holomorphicFunctions U] CoefficientMem.holomorphicSections U (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :=
  (FormFrames.holomorphicCoefficientsFunctionEquivForms U n).symm.trans (FunctionPure.holomorphicPureSectionEquiv U n)

theorem openFormHolomorphicSectionFunctionEquiv_apply (n : ℕ) (a : DeRhamComplex.forms E U n) (x : U) :
    ((openFormHolomorphicSectionFunctionEquiv U n a).val x).val =
      (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n a) x := rfl

theorem openFormHolomorphicSectionFunctionEquiv_restrict (h : V ≤ U) (n : ℕ) (a : DeRhamComplex.forms E U n) :
    openFormHolomorphicSectionFunctionEquiv V n
        (HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a) =
      Restrictions.holomorphicSectionRestrict h (openFormHolomorphicSectionFunctionEquiv U n a) :=
  OpenDomainSheaf.holomorphicFormSectionEquiv_restrict h n a

variable [Fintype ι] [DecidableEq ι]

theorem exists_holomorphicForm_localBasis (n : ℕ) (b : Module.Basis ι ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0))
    (a : ι → DeRhamComplex.forms E U n) (x : U)
    (hx : LinearIndependent ℂ
      (fun j => (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n (a j)) x)) :
    ∃ (V : Opens E) (h : V ≤ U), (x : E) ∈ V ∧
      ∃ c : Module.Basis ι (FunctionPure.holomorphicFunctions V) (DeRhamComplex.forms E V n),
        ∀ j, c j = HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n (a j) := by
  let s := fun j => openFormHolomorphicSectionFunctionEquiv U n (a j)
  have hs : LinearIndependent ℂ (fun j => (s j).val x) :=
    LinearIndependent.of_comp (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).subtype hx
  obtain ⟨V, h, hxV, c, hc⟩ := LocalFrames.exists_holomorphicSection_localBasis b s x hs
  refine ⟨V, h, hxV, c.map (openFormHolomorphicSectionFunctionEquiv V n).symm, ?_⟩
  intro j
  apply (openFormHolomorphicSectionFunctionEquiv V n).injective
  change openFormHolomorphicSectionFunctionEquiv V n
    ((openFormHolomorphicSectionFunctionEquiv V n).symm (c j)) = _
  rw [LinearEquiv.apply_symm_apply, hc]
  exact (openFormHolomorphicSectionFunctionEquiv_restrict h n (a j)).symm

end

/-! Linear independence agrees for the actual covectors and their pure coefficient sections. -/

open _root_.TopologicalSpace

theorem submodule_family_linearIndependent_iff {R N ι : Type} [Ring R] [AddCommGroup N]
    [Module R N] (P : Submodule R N) (v : ι → P) :
    LinearIndependent R v ↔ LinearIndependent R (fun i => (v i).val) := by
  constructor
  · intro h
    exact h.map' P.subtype (Submodule.ker_subtype P)
  · intro h
    exact LinearIndependent.of_comp P.subtype h

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {U : Opens E}

theorem holomorphicCoefficient_linearIndependent_iff (n : ℕ) (a : ι → DeRhamComplex.forms E U n) (x : U) :
    LinearIndependent ℂ (fun i => (openFormHolomorphicSectionFunctionEquiv U n (a i)).val x) ↔
      LinearIndependent ℂ (fun i => (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n (a i)) x) := by
  have h := submodule_family_linearIndependent_iff (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0)
    (fun i => (openFormHolomorphicSectionFunctionEquiv U n (a i)).val x)
  simpa only [openFormHolomorphicSectionFunctionEquiv_apply] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientIndependence
