import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.HigherBootstrap

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The tensor slots for successive directional differentiation are in
reverse list order: the first differentiating direction is the last slot. -/
def reverseDirections : (vs : List E) → Fin vs.length → E
  | [] => Fin.elim0
  | v :: vs => Fin.snoc (reverseDirections vs) v

omit [FiniteDimensional ℝ E] in
theorem iteratedConstantDirectional_eq_tensor (vs : List E)
    {f : E → ℝ} (hf : ContDiff ℝ vs.length f) (x : E) :
    iteratedConstantDirectional f vs x =
      iteratedFDeriv ℝ vs.length f x (reverseDirections vs) := by
  induction vs generalizing f with
  | nil =>
      exact (iteratedFDeriv_zero_apply _).symm
  | cons v vs ih =>
      have hd : ContDiff ℝ vs.length (fderiv ℝ f) :=
        hf.fderiv_right (m := vs.length)
          (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; exact le_rfl)
      have hg : ContDiff ℝ vs.length (constantDirectional f v) :=
        hd.clm_apply contDiff_const
      rw [iteratedConstantDirectional, ih hg]
      change iteratedFDeriv ℝ vs.length (constantDirectional f v) x (reverseDirections vs) =
        iteratedFDeriv ℝ (vs.length+1) f x (Fin.snoc (reverseDirections vs) v)
      rw [iteratedFDeriv_succ_apply_right]
      simp only [Fin.init_snoc, Fin.snoc_last]
      exact congrArg
        (fun B : ContinuousMultilinearMap ℝ (fun _ : Fin vs.length ↦ E) ℝ ↦
          B (reverseDirections vs))
        ((ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left
          hd.contDiffAt (i := vs.length) le_rfl)

omit [FiniteDimensional ℝ E] in
theorem iteratedFDeriv_affine_parameter {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {N : ℕ} {f : E → ℝ} (hf : ContDiff ℝ N f)
    (A : Z →L[ℝ] E) (x : E) (v : Fin N → Z) :
    iteratedFDeriv ℝ N (fun t : Z ↦ f (x+A t)) 0 v =
      iteratedFDeriv ℝ N f x (fun i ↦ A (v i)) := by
  have hs : ContDiff ℝ N (fun y : E ↦ f (x+y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have he := A.iteratedFDeriv_comp_right hs (0 : Z) (i := N) le_rfl
  have hev := congrArg
    (fun B : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z) ℝ ↦ B v) he
  simpa only [Function.comp_def, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left, add_zero] using hev

end OAI.Analysis.PDE.Dirichlet
