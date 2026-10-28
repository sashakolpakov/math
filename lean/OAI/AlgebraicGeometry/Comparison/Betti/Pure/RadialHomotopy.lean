import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorIntegral
import OAI.AlgebraicTopology.DeRham.Comparison.RadialOpenPoincare

/-! # Radial Homotopy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.RadialHomotopy.Holomorphic

noncomputable section

/-! The actual radial integral preserves the pure holomorphic type of forms. -/

open _root_.TopologicalSpace
open scoped Interval

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}

theorem pureCovector_radialIntegrand (form : E → E [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (x : E) (t : ℝ) (hform : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form (t • x))) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (AlgebraicTopology.DeRham.Comparison.RadialOne.radialIntegrand form x t) := by
  have h := CovectorComplexEquiv.Holomorphic.pureCovector_curryLeft (form (t • x)) hform x
  intro z v
  change Fin n → E at v
  change t ^ n • (((form (t • x)).curryLeft x) (fun i => (z : ℂ) • v i)) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * (t ^ n • (((form (t • x)).curryLeft x) v))
  have he := h z v
  change ((form (t • x)).curryLeft x) (fun i => (z : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * ((form (t • x)).curryLeft x) v at he
  rw [he, Complex.real_smul, Complex.real_smul]
  ring

theorem pureCovector_radialHomotopy (form : E → E [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (x : E) (hform : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form (t • x))) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (AlgebraicTopology.DeRham.Comparison.RadialOne.radialHomotopy form x) := by
  apply CovectorIntegral.Holomorphic.pureCovector_intervalIntegral
  intro t ht
  apply pureCovector_radialIntegrand
  exact hform t (by simpa using ht)

variable [FiniteDimensional ℝ E] {U : Opens E}

theorem radialHomotopyForm_pure (hstar : StarConvex ℝ (0 : E) (U : Set E))
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (hform : ∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (form x))
    (x : U) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.radialHomotopyForm hstar form x) := by
  apply pureCovector_radialHomotopy
  intro t ht
  have hm := hstar.smul_mem x.property ht.1 ht.2
  have he := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply form ⟨t • (x : E), hm⟩
  change form.extension (t • (x : E)) = form ⟨t • (x : E), hm⟩ at he
  rw [he]
  exact hform _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.RadialHomotopy.Holomorphic
