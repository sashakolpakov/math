import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParametricInverse

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_slice_right_at {f : Z × E → F} {t : Z} {x : E}
    (hf : DifferentiableAt ℝ f (t, x)) :
    fderiv ℝ (fun y ↦ f (t, y)) x =
      (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ Z E) := by
  have hi : HasFDerivAt (fun y : E ↦ (t, y)) (ContinuousLinearMap.inr ℝ Z E) x := by
    change HasFDerivAt (fun y : E ↦ (t, y))
      ((0 : E →L[ℝ] Z).prod (ContinuousLinearMap.id ℝ E)) x
    simpa only [id_eq] using (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact (hf.hasFDerivAt.comp x hi).fderiv

theorem contDiffOn_slice_fderiv {f : Z × E → F} {I : Set Z}
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (fun p : Z × E ↦ fderiv ℝ (fun y ↦ f (p.1, y)) p.2)
      {p | p.1 ∈ I} := by
  have hopen : IsOpen {p : Z × E | p.1 ∈ I} := hI.preimage continuous_fst
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) {p | p.1 ∈ I} :=
    hf.fderiv_of_isOpen hopen (by simp)
  apply (hd.clm_comp contDiffOn_const).congr
  intro p hp
  exact ParameterDeformation.fderiv_slice_right_at ((hf p hp).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by simp))

def inverseFamily (Φ : Z × E → E) (t : Z) (x : E) : E :=
  Function.invFun (fun y ↦ Φ (t, y)) x

def inverseJacobian (Φ : Z × E → E) (p : Z × E) : E →L[ℝ] E :=
  fderiv ℝ (ParameterDeformation.inverseFamily Φ p.1) (Φ p)

def inverseHessian (Φ : Z × E → E) (p : Z × E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fderiv ℝ (ParameterDeformation.inverseFamily Φ p.1)) (Φ p)

theorem contDiffOn_inverseJacobian {Φ : Z × E → E} {I : Set Z}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : Z × E ↦ ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (ParameterDeformation.inverseJacobian Φ) {p | p.1 ∈ I} := by
  exact (ParameterDeformation.contDiffOn_slice_fderiv hI hi).comp (contDiff_fst.prodMk hΦ).contDiffOn
    (fun p hp ↦ hp)

theorem contDiffOn_inverseHessian {Φ : Z × E → E} {I : Set Z}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : Z × E ↦ ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (ParameterDeformation.inverseHessian Φ) {p | p.1 ∈ I} := by
  exact (ParameterDeformation.contDiffOn_slice_fderiv hI (ParameterDeformation.contDiffOn_slice_fderiv hI hi)).comp
    (contDiff_fst.prodMk hΦ).contDiffOn (fun p hp ↦ hp)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem inverseFamily_equivariant {Φ : Z × E → E} (t : Z)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    ParameterDeformation.inverseFamily Φ t (x + v) = ParameterDeformation.inverseFamily Φ t x + v := by
  apply hb.injective
  change Φ (t, ParameterDeformation.inverseFamily Φ t (x + v)) = Φ (t, ParameterDeformation.inverseFamily Φ t x + v)
  rw [hp]
  exact (Function.invFun_eq (hb.surjective (x + v))).trans
    (congrArg (fun y ↦ y + v) (Function.invFun_eq (hb.surjective x))).symm

theorem fderiv_equivariant {f : E → F} (v : E) (w : F)
    (hp : ∀ x, f (x + v) = f x + w) (x : E) :
    fderiv ℝ f (x + v) = fderiv ℝ f x := by
  have he : (fun y ↦ f (y + v)) = fun y ↦ f y + w := funext hp
  calc
    _ = fderiv ℝ (fun y ↦ f (y + v)) x := (fderiv_comp_add_right v).symm
    _ = fderiv ℝ (fun y ↦ f y + w) x := by rw [he]
    _ = _ := fderiv_add_const w

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem inverseJacobian_periodic {Φ : Z × E → E} (t : Z)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    ParameterDeformation.inverseJacobian Φ (t, x + v) = ParameterDeformation.inverseJacobian Φ (t, x) := by
  change fderiv ℝ (ParameterDeformation.inverseFamily Φ t) (Φ (t, x + v)) = _
  rw [hp]
  exact ParameterDeformation.fderiv_equivariant v v (ParameterDeformation.inverseFamily_equivariant t hb v hp) _

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem inverseHessian_periodic {Φ : Z × E → E} (t : Z)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    ParameterDeformation.inverseHessian Φ (t, x + v) = ParameterDeformation.inverseHessian Φ (t, x) := by
  change fderiv ℝ (fderiv ℝ (ParameterDeformation.inverseFamily Φ t)) (Φ (t, x + v)) = _
  rw [hp]
  apply ParameterDeformation.fderiv_equivariant v 0
  intro y
  rw [add_zero]
  exact ParameterDeformation.fderiv_equivariant v v (ParameterDeformation.inverseFamily_equivariant t hb v hp) y

omit [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem inverseFamily_zero {Φ : Z × E → E} (hzero : ∀ x, Φ (0, x) = x) :
    ParameterDeformation.inverseFamily Φ 0 = id := by
  funext x
  change ParameterDeformation.inverseFamily Φ 0 x = x
  have he : Φ (0, ParameterDeformation.inverseFamily Φ 0 x) = x :=
    Function.invFun_eq (show ∃ y, Φ (0, y) = x from ⟨x, hzero x⟩)
  exact (hzero (ParameterDeformation.inverseFamily Φ 0 x)).symm.trans he

omit [NormedSpace ℝ Z] in
theorem inverseJacobian_zero {Φ : Z × E → E} (hzero : ∀ x, Φ (0, x) = x) (x : E) :
    ParameterDeformation.inverseJacobian Φ (0, x) = ContinuousLinearMap.id ℝ E := by
  change fderiv ℝ (ParameterDeformation.inverseFamily Φ 0) (Φ (0, x)) = _
  rw [ParameterDeformation.inverseFamily_zero hzero, fderiv_id]

omit [NormedSpace ℝ Z] in
theorem inverseHessian_zero {Φ : Z × E → E} (hzero : ∀ x, Φ (0, x) = x) (x : E) :
    ParameterDeformation.inverseHessian Φ (0, x) = 0 := by
  change fderiv ℝ (fderiv ℝ (ParameterDeformation.inverseFamily Φ 0)) (Φ (0, x)) = 0
  rw [ParameterDeformation.inverseFamily_zero hzero]
  have he : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  rw [he, fderiv_const_apply]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem inverseFamily_preserves_level {Φ : Z × E → E} (t : Z)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (r : E → ℝ)
    (hr : ∀ x, r (Φ (t, x)) = r x) (x : E) :
    r (ParameterDeformation.inverseFamily Φ t x) = r x := by
  have he := Function.invFun_eq (hb.surjective x)
  calc
    r (ParameterDeformation.inverseFamily Φ t x) = r (Φ (t, ParameterDeformation.inverseFamily Φ t x)) := (hr _).symm
    _ = r x := congrArg r he

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
