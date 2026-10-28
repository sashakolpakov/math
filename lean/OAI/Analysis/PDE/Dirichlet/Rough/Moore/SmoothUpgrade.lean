import OAI.Analysis.PDE.Dirichlet.Rough.Moore.SmoothData
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.IFT
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Global

noncomputable section
open Set Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace n 4

omit [FiniteDimensional ℝ P] in
/-- A positive classical C³ solution of the smooth periodic Moore
Dirichlet problem has one globally smooth periodic representative, with
its full two-jet preserved on the closed domain. All geometric families,
the linear inverse, normal regularity, and smooth extension are proved
internally rather than supplied as premises. -/
theorem exists_smooth_periodic_moore_representative [Nontrivial E]
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (B₀ f ψ : E → ℝ) (hB₀ : ContDiff ℝ ∞ B₀) (hf : ContDiff ℝ ∞ f)
    (hψ : ContDiff ℝ 3 ψ)
    (hB₀p : LatticePeriodic e b B₀) (hfp : LatticePeriodic e b f)
    (hψp : LatticePeriodic e b ψ) (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LatticePeriodic e b g ∧
      (∀ x, r x ≤ 0 → g x = ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ g x = fderiv ℝ ψ x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ ψ) x) := by
  classical
  by_cases hne : Nonempty {x | r x ≤ 0}
  · let := hne
    let hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0} :=
      fun x (hx : r x < 0) ↦ (show r x ≤ 0 from hx.le)
    have hα : (0 : ℝ) < 1/2 := by norm_num
    have hα1 : (1/2 : ℝ) < 1 := by norm_num
    have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
      rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
    obtain ⟨B,u,hBp,hB₂,hψ₂⟩ := exists_smooth_moore_jet_data (hΩK := hΩD)
      hK hr hrp hbounded hα hα1 B₀ ψ (hB₀.of_le (by simp)) hψ hB₀p hψp hψbd
    have hinv := smooth_moore_data_invertible hn hK hr hrp hbounded hreg hrpos
      hα hα1 ψ hψ hψp hpos hclosure B u hBp hψ₂
    have hfamily (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] :
        OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasGeometricSolutionFamilies (Z := Z) e b r ψ B₀ hΩD (1/2) := by
      exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.hasGeometricSolutionFamilies_of_invertible
        hn hK hr hrp hbounded hreg (fun x hx ↦ hrpos x hx.le) hα hα1.le
        B₀ f hB₀ hf hB₀p hfp B hBp hB₂ u ψ (hψ.of_le (by norm_num)) hψp hψbd
        hψ₂ hpos heq (isOpen_lt hr.continuous continuous_const) hclosure hinv
    exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.exists_smooth_periodic_representative_of_parameter_families
      hn hK (hfamily E) (fun k ↦ hfamily (EuclideanSpace.proj k).ker)
      hr hrp hbounded hreg (hψ.of_le (by norm_num)) hψp hB₀ f hf hpos heq
  · refine ⟨fun _ ↦ 0,contDiff_const,(fun _ _ ↦ rfl),?_,?_,?_⟩ <;>
      intro x hx <;> exact False.elim (hne ⟨⟨x,hx⟩⟩)

end OAI.Analysis.PDE.Dirichlet
