import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ClosedExtraction

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only finitely many directional germs are needed, so the parameterized
chart flows can be restricted to one common spatial neighborhood. -/
theorem exists_common_contDiffOn_neighborhood {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {x : E} {q : ℕ∞ω} (f : ι → E → F)
    (h : ∀ i, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ContDiffOn ℝ q (f i) (S ∩ O)) :
    ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∀ i, ContDiffOn ℝ q (f i) (S ∩ O) := by
  classical
  choose O hO hx hf using h
  refine ⟨⋂ i, O i, isOpen_iInter_of_finite hO, by simpa using hx, ?_⟩
  intro i
  exact (hf i).mono (fun y hy ↦ ⟨hy.1,mem_iInter.mp hy.2 i⟩)

theorem tangent_basis_sum {ι : Type*} [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker) (v : ℓ.ker) :
    (∑ i, b.repr v i • (b i : E)) = v := by
  have h := congrArg ℓ.ker.subtype (b.sum_repr v)
  simpa only [map_sum,map_smul,Submodule.subtype_apply] using h

theorem contDiffOn_tangents_of_basis {ι : Type*} [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker) {S : Set E} {q : ℕ∞ω}
    (f : E → ℝ) (hb : ∀ i, ContDiffOn ℝ q (constantDirectional f (b i)) S) :
    ∀ v, ℓ v = 0 → ContDiffOn ℝ q (constantDirectional f v) S := by
  classical
  intro v hv
  let w : ℓ.ker := ⟨v,hv⟩
  have he : constantDirectional f v = fun x ↦ ∑ i, b.repr w i * constantDirectional f (b i) x := by
    funext x
    change fderiv ℝ f x (w : E) = _
    rw [← tangent_basis_sum ℓ b w, map_sum]
    simp only [map_smul,smul_eq_mul,constantDirectional]
  rw [he]
  exact ContDiffOn.sum (fun i _ ↦ contDiffOn_const.mul (hb i))

theorem contDiffOn_bilinear_tangents_of_basis {ι : Type*} [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker) {S : Set E} {q : ℕ∞ω}
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i j, ContDiffOn ℝ q (fun x ↦ B x (b i) (b j)) S) :
    ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 → ContDiffOn ℝ q (fun x ↦ B x v w) S := by
  classical
  intro v hv w hw
  let v' : ℓ.ker := ⟨v,hv⟩
  let w' : ℓ.ker := ⟨w,hw⟩
  have he : (fun x ↦ B x v w) = fun x ↦
      ∑ i, ∑ j, b.repr v' i * (b.repr w' j * B x (b i) (b j)) := by
    funext x
    change B x (v' : E) (w' : E) = _
    conv_lhs => rw [← tangent_basis_sum ℓ b v', ← tangent_basis_sum ℓ b w']
    simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [he]
  exact ContDiffOn.sum (fun i _ ↦ ContDiffOn.sum (fun j _ ↦
    contDiffOn_const.mul (contDiffOn_const.mul (hb i j))))

theorem contDiffOn_hessian_mixed_of_diagonals
    {S : Set E} {q : ℕ∞ω} {f : E → ℝ} (hf : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (v w : E)
    (hv : ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x v v) S)
    (hw : ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x w w) S)
    (hs : ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x (v+w) (v+w)) S) :
    ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x v w) S := by
  have hc : ContDiffOn ℝ q (fun x ↦ (1/2 : ℝ) *
      ((fderiv ℝ (fderiv ℝ f) x (v+w) (v+w) - fderiv ℝ (fderiv ℝ f) x v v) -
        fderiv ℝ (fderiv ℝ f) x w w)) S := contDiffOn_const.mul ((hs.sub hv).sub hw)
  apply hc.congr
  intro x hx
  have hsym := ((hf x hx).isSymmSndFDerivAt (by norm_num)).eq v w
  simp only [map_add,add_apply]
  linarith

theorem contDiffOn_second_tangents_of_diagonal_basis {ι : Type*} [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker) {S : Set E} {q : ℕ∞ω}
    {f : E → ℝ} (hf : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (hd : ∀ i, ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b i)) S)
    (hs : ∀ i j, ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x
      ((b i : E) + b j) ((b i : E) + b j)) S) :
    ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
      ContDiffOn ℝ q (constantDirectional (constantDirectional f v) w) S := by
  have hb (i j : ι) : ContDiffOn ℝ q (fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j)) S :=
    contDiffOn_hessian_mixed_of_diagonals hf (b i) (b j) (hd i) (hd j) (hs i j)
  intro v hv w hw
  apply (contDiffOn_bilinear_tangents_of_basis ℓ b (fderiv ℝ (fderiv ℝ f)) hb w hw v hv).congr
  intro x hx
  exact fderiv_constantDirectional_apply (hf x hx) v w

end OAI.Analysis.PDE.Dirichlet
