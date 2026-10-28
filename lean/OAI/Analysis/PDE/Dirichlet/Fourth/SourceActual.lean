import OAI.Analysis.PDE.Dirichlet.Fourth.SourceBound

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

variable {I X : Type} [Fintype I] [DecidableEq I] [MetricSpace X] {α : ℝ}
local notation "E" => EuclideanSpace ℝ I
attribute [local instance] sourceBoundMatrixValueGroup sourceBoundMatrixValueSpace
  sourceBoundScalar1Group sourceBoundScalar1Space sourceBoundScalar2Group sourceBoundScalar2Space
  sourceBoundScalar3Group sourceBoundScalar3Space sourceBoundVector1Group sourceBoundVector1Space
  sourceBoundVector2Group sourceBoundVector2Space sourceBoundVector3Group sourceBoundVector3Space
  sourceBoundMatrixGroup sourceBoundMatrixSpace sourceBoundFirstGroup sourceBoundFirstSpace
  sourceBoundRestGroup sourceBoundRestSpace sourceBoundFullGroup sourceBoundFullSpace

omit [DecidableEq I] in
/-- Exact identification of the constructed Hölder jet with actual derivatives.
Every derivative of the unknown appearing here has order at most three. -/
theorem secondFieldJetHolder_actual (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix I I ℝ) α) (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix I I ℝ) α)
    (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (T3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (S0 : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (S1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (S2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (F2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (a : E → Matrix I I ℝ) (u f : E → ℝ) (T S : E → E) (x : X) (y : E)
    (hA : OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a y) (hDA : OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ a y)
    (hU1 : OAI.Analysis.Normed.Function.Holder.HolderMap.value U1 x = fderiv ℝ u y) (hU2 : OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x = fderiv ℝ (fderiv ℝ u) y)
    (hU3 : OAI.Analysis.Normed.Function.Holder.HolderMap.value U3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y)
    (hT0 : OAI.Analysis.Normed.Function.Holder.HolderMap.value T0 x = T y) (hT1 : OAI.Analysis.Normed.Function.Holder.HolderMap.value T1 x = fderiv ℝ T y)
    (hT2 : OAI.Analysis.Normed.Function.Holder.HolderMap.value T2 x = fderiv ℝ (fderiv ℝ T) y)
    (hT3 : OAI.Analysis.Normed.Function.Holder.HolderMap.value T3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ T)) y)
    (hS0 : OAI.Analysis.Normed.Function.Holder.HolderMap.value S0 x = S y) (hS1 : OAI.Analysis.Normed.Function.Holder.HolderMap.value S1 x = fderiv ℝ S y)
    (hS2 : OAI.Analysis.Normed.Function.Holder.HolderMap.value S2 x = fderiv ℝ (fderiv ℝ S) y)
    (hF1 : OAI.Analysis.Normed.Function.Holder.HolderMap.value F1 x = fderiv ℝ f y) (hF2 : OAI.Analysis.Normed.Function.Holder.HolderMap.value F2 x = fderiv ℝ (fderiv ℝ f) y) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F := SecondFieldSourceJet I)
      (secondFieldJetHolder (I := I) (X := X) hα A DA U1 U2 U3 T0 T1 T2 T3 S0 S1 S2 F1 F2) x =
      secondFieldSourceJet a u f T S y := by
  have he : OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα DA S0) x = (fderiv ℝ a y) (S y) := by
    change (OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value S0 x) = _
    rw [hDA,hS0]
  simp only [secondFieldJetHolder, firstFieldJetHolder, OAI.Analysis.Normed.Function.Holder.HolderMap.value_pair, OAI.Analysis.Normed.Function.Holder.HolderMap.value_action,
    he, hA, hDA, hU1, hU2, hU3, hT0, hT1, hT2, hT3, hS0, hS1, hS2, hF1, hF2,
    secondFieldSourceJet, firstFieldJet, firstFieldJetDifferential, secondFieldRestJet,
    ContinuousLinearMap.prod_apply]

/-- A uniform bound for the actual twice-tangential Moore forcing. The input
jet is exactly the lower-jet bundle constructed above, not an assumed source
estimate; in particular it has no fourth derivative of the potential. -/
theorem exists_moore_second_source_bound_of_jet {n : ℕ}
    (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u f : CoordinateSpace n 4 → ℝ)
        (T S : CoordinateSpace n 4 → CoordinateSpace n 4),
        ContDiff ℝ 3 u → ContDiff ℝ 2 f → ContDiff ℝ 3 T →
        ∀ (ι : X → CoordinateSpace n 4)
          (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (SecondFieldSourceJet (Fin n × Fin 4)) α), ‖J‖ ≤ R →
          (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = secondFieldSourceJet
            (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
              u f T S (ι x)) →
          ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α,
            (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = mooreSecondFieldForcing u f T S (ι x)) ∧ ‖F‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_secondFieldExpression_holder_bound
    (I := Fin n × Fin 4) (X := X) hα hR
  refine ⟨C, hC, ?_⟩
  intro u f T S hu hf hT ι J hJ hval
  obtain ⟨F, hF, hFn⟩ := hbound J hJ
  refine ⟨F, ?_, hFn⟩
  intro x
  rw [hF x, hval x, ← mooreSecondFieldForcing_eq_expression u f T S hu hf hT]

end OAI.Analysis.PDE.Dirichlet
