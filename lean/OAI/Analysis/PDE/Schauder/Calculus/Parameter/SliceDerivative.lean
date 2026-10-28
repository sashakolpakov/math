import OAI.Analysis.PDE.Schauder.Calculus.SliceDerivative

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {Z X Y W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem coe_parameter_partial_fderiv_of_slice
    (L : Y →L[ℝ] W) (Q : Z × X → Y) (F : X → W) (M : X →L[ℝ] W)
    (z : Z) (x : X)
    (hQ : DifferentiableAt ℝ Q (z,x)) (hF : HasFDerivAt F M x)
    (he : ∀ y, L (Q (z,y)) = F y) :
    L.comp ((fderiv ℝ Q (z,x)).comp (ContinuousLinearMap.inr ℝ Z X)) = M := by
  have hi : HasFDerivAt (fun y : X => (z,y)) (ContinuousLinearMap.inr ℝ Z X) x := by
    change HasFDerivAt (fun y : X => (z,y))
      ((0 : X →L[ℝ] Z).prod (ContinuousLinearMap.id ℝ X)) x
    simpa only [id_eq] using (hasFDerivAt_const z x).prodMk (hasFDerivAt_id x)
  have hs := hQ.hasFDerivAt.comp x hi
  have hl := L.hasFDerivAt.comp x hs
  have hfun : (fun y : X => L (Q (z,y))) = F := funext he
  change HasFDerivAt (fun y : X => L (Q (z,y))) _ x at hl
  rw [hfun] at hl
  exact hl.unique hF

end OAI.Analysis.PDE.Schauder
