import OAI.Analysis.PDE.Weak.Elliptic.Product
import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient
import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
import OAI.Analysis.PDE.Dirichlet.Derivative

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem fderiv_cellGradient_comm {φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient φ) x v =
      OAI.Analysis.PDE.Variational.cellGradient (fun y ↦ fderiv ℝ φ y v) x := by
  ext i
  have hi := ((EuclideanSpace.proj i).hasFDerivAt.comp x
    ((contDiff_cellGradient hφ).differentiable (by simp) x).hasFDerivAt).fderiv
  have he : fderiv ℝ (fun y ↦ OAI.Analysis.PDE.Variational.cellGradient φ y i) x v =
      (fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient φ) x v) i := by
    exact congrArg (fun L ↦ L v) hi
  rw [← he]
  exact OAI.Analysis.PDE.Dirichlet.directionalDerivative_comm (hφ.of_le (by simp)) v (Pi.single i 1) x

theorem tsupport_cellGradient_subset (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) :
    tsupport (OAI.Analysis.PDE.Variational.cellGradient φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  apply hx
  ext i
  simp [OAI.Analysis.PDE.Variational.cellGradient, fderiv_of_notMem_tsupport ℝ hn]

/-- Distributional differentiation of the actual divergence equation.
This uses the commutation of the classical derivatives only on the test
function, not on the weak solution. -/
theorem WeakDivergenceEquation.differentiate
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    {H Hd : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {f fd : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω H f)
    (hH : HasWeakDirectionalDerivativeOn volume Ω v H Hd)
    (hf : HasWeakDirectionalDerivativeOn volume Ω v f fd) :
    WeakDivergenceEquation Ω Hd fd := by
  intro φ hφ hs hsub
  have hψ : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hψs : HasCompactSupport (fun x ↦ fderiv ℝ φ x v) := hs.fderiv_apply ℝ v
  have hψsub : tsupport (fun x ↦ fderiv ℝ φ x v) ⊆ Ω := by
    apply Subset.trans (b := tsupport φ) _ hsub
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    apply support_fderiv_subset ℝ
    intro hz
    apply hx
    change fderiv ℝ φ x v = 0
    rw [hz, zero_apply]
  have heH := hH (OAI.Analysis.PDE.Variational.cellGradient φ) ((contDiff_cellGradient hφ).of_le (by simp))
    (hasCompactSupport_cellGradient hs) ((tsupport_cellGradient_subset φ).trans hsub)
  have hef := hf φ (hφ.of_le (by simp)) hs hsub
  simp only [RCLike.inner_apply, conj_trivial] at hef
  have hef' : (∫ x, fd x * φ x) = -(∫ x, f x * fderiv ℝ φ x v) := by
    simpa only [mul_comm] using hef
  simp_rw [fderiv_cellGradient_comm hφ] at heH
  rw [hweak _ hψ hψs hψsub] at heH
  exact heH.trans hef'.symm

/-- In particular, differentiating a variable-coefficient equation yields
the true differentiated flux, including its coefficient commutator. -/
theorem WeakDivergenceEquation.differentiate_coefficient
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A)
    (G Gj : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {f fd : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (G x)) f)
    (hG : HasWeakDirectionalDerivativeOn volume Ω v G Gj)
    (hf : HasWeakDirectionalDerivativeOn volume Ω v f fd) :
    WeakDivergenceEquation Ω
      (fun x ↦ A x (Gj x) + fderiv ℝ A x v (G x)) fd :=
  hweak.differentiate (hG.operator_apply volume A hA G Gj) hf

end OAI.Analysis.PDE.Weak
