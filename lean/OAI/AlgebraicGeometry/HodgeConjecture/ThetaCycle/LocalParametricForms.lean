import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricJets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothConvergence

/-! # Local Parametric Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricForms.CM

noncomputable section

/-! ThetaCycle: local smooth parameter expressions in the actual atlas imply
convergence in the full manifold smooth-form topology. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

theorem local_parametric_forms_converge
    {P E M A : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    [TopologicalSpace M] [ChartedSpace E M]
    {l : Filter A} (p : A → P) (p₀ : P) (hp : Tendsto p l (𝓝 p₀))
    (n : ℕ) (forms : A → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (hlocal : ∀ e : SmoothTopology.CM.SmoothAtlasChart E M, ∀ x ∈ e.val.target,
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ g : P → E → E [⋀^Fin n]→L[ℝ] ℂ,
          (∀ y ∈ U, ContDiffAt ℝ ∞ (Function.uncurry g) (p₀, y)) ∧
          (∀ᶠ a in l, ∀ y ∈ U, (forms a).val.inChart e.val y = g (p a) y) ∧
          (∀ y ∈ U, form.val.inChart e.val y = g p₀ y)) :
    let _ := SmoothTopology.CM.smoothFormTopology E M n
    Tendsto forms l (𝓝 form) := by
  apply (SmoothConvergence.CM.tendsto_smooth_iff_compact_derivatives l forms form).mpr
  intro e m C hC
  let K : Set E := Subtype.val '' C
  have hK : IsCompact K := hC.image continuous_subtype_val
  have hKS : K ⊆ e.val.target := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  have hu := LocalParametricJets.CM.locally_parametric_uniform_derivatives p p₀ hp
    (fun a => (forms a).val.inChart e.val) (form.val.inChart e.val) e.val.target
    (hlocal e) m K hK hKS
  exact (hu.comp Subtype.val).mono (fun y hy => ⟨y, hy, rfl⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricForms.CM
