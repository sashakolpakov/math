import Mathlib

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {X Y W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem coe_partial_fderiv_of_slice
    (L : Y →L[ℝ] W) (Q : ℝ × X → Y) (F : X → W) (M : X →L[ℝ] W) (x : X)
    (hQ : DifferentiableAt ℝ Q (0,x)) (hF : HasFDerivAt F M x)
    (he : ∀ y, L (Q (0,y)) = F y) :
    L.comp ((fderiv ℝ Q (0,x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) = M := by
  have hi : HasFDerivAt (fun y : X => ((0:ℝ),y)) (ContinuousLinearMap.inr ℝ ℝ X) x := by
    change HasFDerivAt (fun y : X => ((0:ℝ),y))
      ((0 : X →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ X)) x
    simpa only [id_eq] using (hasFDerivAt_const (0:ℝ) x).prodMk (hasFDerivAt_id x)
  have hs := hQ.hasFDerivAt.comp x hi
  have hl := L.hasFDerivAt.comp x hs
  have hfun : (fun y : X => L (Q (0,y))) = F := funext he
  change HasFDerivAt (fun y : X => L (Q (0,y))) _ x at hl
  rw [hfun] at hl
  exact hl.unique hF

theorem hasFDerivAt_affine_map_sub
    (L : X →L[ℝ] Y) (F : Y → W) (a : Y) (c : W) (x : X)
    (hF : DifferentiableAt ℝ F (a+L x)) :
    HasFDerivAt (fun y => F (a+L y)-c) ((fderiv ℝ F (a+L x)).comp L) x :=
  (hF.hasFDerivAt.comp x (L.hasFDerivAt.const_add a)).sub_const c

theorem hasFDerivAt_affine_factorization
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (M : Z →L[ℝ] Y) (L : X →L[ℝ] Y) (pin : X →L[ℝ] Z)
    (F : Y → W) (a : Y) (c : W) (x : X) (g : Z)
    (hML : M.comp pin = L) (hbase : a+L x=M g)
    (hF : DifferentiableAt ℝ F (M g)) :
    HasFDerivAt (fun y => F (a+L y)-c) ((fderiv ℝ (F ∘ M) g).comp pin) x := by
  have hm : HasFDerivAt (F ∘ M) ((fderiv ℝ F (M g)).comp M) g :=
    hF.hasFDerivAt.comp g M.hasFDerivAt
  rw [hm.fderiv,ContinuousLinearMap.comp_assoc,hML]
  have ha : DifferentiableAt ℝ F (a+L x) := by rw [hbase]; exact hF
  have hh := hasFDerivAt_affine_map_sub L F a c x ha
  simpa only [hbase] using hh

end OAI.Analysis.PDE.Schauder
