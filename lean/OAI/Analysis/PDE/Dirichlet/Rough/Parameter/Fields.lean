import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.GeometricFamilies
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.JetFields
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Fields

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [CompleteSpace Z] in
/-- The genuine parameter-dependent geometric change of coordinates
supplies all actual coefficients of the smooth Hölder-valued Moore map. -/
theorem PeriodicDomainDeformation.exists_parameter_fields
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r : E → ℝ}
    (D : ParameterDeformation.PeriodicDomainDeformation (Z := Z) e b r) {K : Set V} (hK : IsCompact K)
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (B f : E → ℝ) (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f)
    (hBp : LatticePeriodic e b (fderiv ℝ (fderiv ℝ B))) (hfp : LatticePeriodic e b f) :
    ∃ C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α {t : Z | ‖t‖ < D.radius} e b,
      (∀ t, ‖t‖ < D.radius → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian t) x =
        ParameterDeformation.inverseJacobian D.map (t,x)) ∧
      (∀ t, ‖t‖ < D.radius → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature t) x =
        ParameterDeformation.inverseHessian D.map (t,x)) ∧
      (∀ t, ‖t‖ < D.radius → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x =
        fderiv ℝ (fderiv ℝ B) (D.map (t,x))) ∧
      (∀ t, ‖t‖ < D.radius → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) x = f (D.map (t,x))) := by
  have hI : IsOpen {t : Z | ‖t‖ < D.radius} := isOpen_lt continuous_norm continuous_const
  have hJ := ParameterDeformation.contDiffOn_inverseJacobian hI D.smooth D.inverse_smooth
  have hT := ParameterDeformation.contDiffOn_inverseHessian hI D.smooth D.inverse_smooth
  have hpJ (t : Z) (ht : ‖t‖ < D.radius) :
      LatticePeriodic e b (fun x ↦ ParameterDeformation.inverseJacobian D.map (t,x)) := by
    intro x l
    rw [lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
    exact ParameterDeformation.inverseJacobian_periodic t (D.bijective t ht) _ (D.equivariant t l) x
  have hpT (t : Z) (ht : ‖t‖ < D.radius) :
      LatticePeriodic e b (fun x ↦ ParameterDeformation.inverseHessian D.map (t,x)) := by
    intro x l
    rw [lattice_translate_eq,add_comm (e.symm ((l:P),0)) x]
    exact ParameterDeformation.inverseHessian_periodic t (D.bijective t ht) _ (D.equivariant t l) x
  have hBB : ContDiff ℝ ∞ (fun p ↦ fderiv ℝ (fderiv ℝ B) (D.map p)) :=
    ((hB.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp D.smooth
  exact OAI.Analysis.PDE.Schauder.exists_parameterJetFields e b hK hr hrp hbounded hα hα1 hI
    (ParameterDeformation.inverseJacobian D.map) (ParameterDeformation.inverseHessian D.map)
    (fun p ↦ fderiv ℝ (fderiv ℝ B) (D.map p)) (fun p ↦ f (D.map p))
    hJ hT hBB.contDiffOn (hf.comp D.smooth).contDiffOn hpJ hpT
    (fun t _ ↦ OAI.Analysis.PDE.Schauder.latticePeriodic_comp_equivariant e b hBp _ (D.equivariant t))
    (fun t _ ↦ OAI.Analysis.PDE.Schauder.latticePeriodic_comp_equivariant e b hfp _ (D.equivariant t))

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
