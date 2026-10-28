import OAI.Analysis.PDE.Dirichlet.Fourth.CoefficientJet

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

variable {n : ℕ} {X : Type} [MetricSpace X] {α : ℝ}
local notation "E" => CoordinateSpace n 4
attribute [local instance] coefficientJetMatrixValueGroup coefficientJetMatrixValueSpace
  coefficientJetFirstGroup coefficientJetFirstSpace coefficientJetSecondGroup coefficientJetSecondSpace
  coefficientJetThirdGroup coefficientJetThirdSpace coefficientJetMatrixGroup coefficientJetMatrixSpace

/-- The smooth finite-jet bounds applied to actual potential derivatives. -/
theorem exists_actual_mooreCoefficient_jet_holder_bound {R : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E → ℝ), ContDiff ℝ 3 u → ∀ (ι : X → E)
      (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
      (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α),
      ‖U2‖ ≤ R → ‖U3‖ ≤ R →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x = fderiv ℝ (fderiv ℝ u) (ι x)) →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (ι x)) →
      ∃ (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
        (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (ι x))) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ
          (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) (ι x)) ∧
        ‖A‖ ≤ C ∧ ‖DA‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_mooreCoefficient_jet_holder_bound (n := n) (X := X) hα hR
  refine ⟨C,hC,?_⟩
  intro u hu ι U2 U3 hU2 hU3 eU2 eU3
  obtain ⟨A,DA,eA,eDA,nA,nDA⟩ := hbound U2 U3 hU2 hU3
  refine ⟨A,DA,?_,?_,nA,nDA⟩
  · intro x
    rw [eA x,eU2 x,mooreCoefficientJetMap_actual]
  · intro x
    rw [eDA x,eU2 x,eU3 x,mooreCoefficientDerivativeJetMap_actual u hu]

end OAI.Analysis.PDE.Dirichlet
