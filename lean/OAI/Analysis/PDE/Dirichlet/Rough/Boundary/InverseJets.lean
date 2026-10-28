import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParametricInverse

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_slice_right_at {f : ℝ × E → F} {t : ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (t, x)) :
    fderiv ℝ (fun y ↦ f (t, y)) x =
      (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hi : HasFDerivAt (fun y : E ↦ (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    change HasFDerivAt (fun y : E ↦ (t, y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) x
    simpa only [id_eq] using (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact (hf.hasFDerivAt.comp x hi).fderiv

theorem contDiffOn_slice_fderiv {f : ℝ × E → F} {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ fderiv ℝ (fun y ↦ f (p.1, y)) p.2)
      {p | p.1 ∈ I} := by
  have hopen : IsOpen {p : ℝ × E | p.1 ∈ I} := hI.preimage continuous_fst
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) {p | p.1 ∈ I} :=
    hf.fderiv_of_isOpen hopen (by simp)
  apply (hd.clm_comp contDiffOn_const).congr
  intro p hp
  exact fderiv_slice_right_at ((hf p hp).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by simp))

def inverseFamily (Φ : ℝ × E → E) (t : ℝ) (x : E) : E :=
  Function.invFun (fun y ↦ Φ (t, y)) x

def inverseJacobian (Φ : ℝ × E → E) (p : ℝ × E) : E →L[ℝ] E :=
  fderiv ℝ (inverseFamily Φ p.1) (Φ p)

def inverseHessian (Φ : ℝ × E → E) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fderiv ℝ (inverseFamily Φ p.1)) (Φ p)

theorem contDiffOn_inverseJacobian {Φ : ℝ × E → E} {I : Set ℝ}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ inverseFamily Φ p.1 p.2) {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (inverseJacobian Φ) {p | p.1 ∈ I} := by
  exact (contDiffOn_slice_fderiv hI hi).comp (contDiff_fst.prodMk hΦ).contDiffOn
    (fun p hp ↦ hp)

theorem contDiffOn_inverseHessian {Φ : ℝ × E → E} {I : Set ℝ}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ inverseFamily Φ p.1 p.2) {p | p.1 ∈ I}) :
    ContDiffOn ℝ ∞ (inverseHessian Φ) {p | p.1 ∈ I} := by
  exact (contDiffOn_slice_fderiv hI (contDiffOn_slice_fderiv hI hi)).comp
    (contDiff_fst.prodMk hΦ).contDiffOn (fun p hp ↦ hp)

omit [NormedSpace ℝ E] in
theorem inverseFamily_equivariant {Φ : ℝ × E → E} (t : ℝ)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    inverseFamily Φ t (x + v) = inverseFamily Φ t x + v := by
  apply hb.injective
  change Φ (t, inverseFamily Φ t (x + v)) = Φ (t, inverseFamily Φ t x + v)
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

theorem inverseJacobian_periodic {Φ : ℝ × E → E} (t : ℝ)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    inverseJacobian Φ (t, x + v) = inverseJacobian Φ (t, x) := by
  change fderiv ℝ (inverseFamily Φ t) (Φ (t, x + v)) = _
  rw [hp]
  exact fderiv_equivariant v v (inverseFamily_equivariant t hb v hp) _

theorem inverseHessian_periodic {Φ : ℝ × E → E} (t : ℝ)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (v : E)
    (hp : ∀ x, Φ (t, x + v) = Φ (t, x) + v) (x : E) :
    inverseHessian Φ (t, x + v) = inverseHessian Φ (t, x) := by
  change fderiv ℝ (fderiv ℝ (inverseFamily Φ t)) (Φ (t, x + v)) = _
  rw [hp]
  apply fderiv_equivariant v 0
  intro y
  rw [add_zero]
  exact fderiv_equivariant v v (inverseFamily_equivariant t hb v hp) y

omit [NormedSpace ℝ E] in
theorem inverseFamily_zero {Φ : ℝ × E → E} (hzero : ∀ x, Φ (0, x) = x) :
    inverseFamily Φ 0 = id := by
  funext x
  change inverseFamily Φ 0 x = x
  have he : Φ (0, inverseFamily Φ 0 x) = x :=
    Function.invFun_eq (show ∃ y, Φ (0, y) = x from ⟨x, hzero x⟩)
  exact (hzero (inverseFamily Φ 0 x)).symm.trans he

theorem inverseJacobian_zero {Φ : ℝ × E → E} (hzero : ∀ x, Φ (0, x) = x) (x : E) :
    inverseJacobian Φ (0, x) = ContinuousLinearMap.id ℝ E := by
  change fderiv ℝ (inverseFamily Φ 0) (Φ (0, x)) = _
  rw [inverseFamily_zero hzero, fderiv_id]

theorem inverseHessian_zero {Φ : ℝ × E → E} (hzero : ∀ x, Φ (0, x) = x) (x : E) :
    inverseHessian Φ (0, x) = 0 := by
  change fderiv ℝ (fderiv ℝ (inverseFamily Φ 0)) (Φ (0, x)) = 0
  rw [inverseFamily_zero hzero]
  have he : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  rw [he, fderiv_const_apply]

omit [NormedSpace ℝ E] in
theorem inverseFamily_preserves_level {Φ : ℝ × E → E} (t : ℝ)
    (hb : Function.Bijective (fun x ↦ Φ (t, x))) (r : E → ℝ)
    (hr : ∀ x, r (Φ (t, x)) = r x) (x : E) :
    r (inverseFamily Φ t x) = r x := by
  have he := Function.invFun_eq (hb.surjective x)
  calc
    r (inverseFamily Φ t x) = r (Φ (t, inverseFamily Φ t x)) := (hr _).symm
    _ = r x := congrArg r he

end OAI.Analysis.PDE.Dirichlet
