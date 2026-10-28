import OAI.Analysis.PDE.Weak.Boundary.Weak.Scalar
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Reassembling scalar distributional derivatives into the actual
Euclidean-valued weak derivative. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem HasWeakDirectionalDerivativeOn.of_scalar_components
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {w : OAI.Analysis.PDE.Variational.CellCoordinates m}
    {u g : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hd : ∀ j, HasWeakDirectionalDerivativeOn volume Ω w (fun x => u x j) (fun x => g x j)) :
    HasWeakDirectionalDerivativeOn volume Ω w u g := by
  intro φ hφ hs hsub
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  let pr (j : Fin (m + 1)) : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp e
  have hpr (j) (z : OAI.Analysis.PDE.Variational.CellVectors m) : pr j z = z j := rfl
  have hc (j) : ContDiff ℝ 1 (fun x => φ x j) := (pr j).contDiff.comp hφ
  have hcs (j) : HasCompactSupport (fun x => φ x j) := hs.comp_left (map_zero (pr j))
  have hcsub (j) : tsupport (fun x => φ x j) ⊆ Ω := by
    apply Subset.trans (b := tsupport φ) _ hsub
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    have hz := image_eq_zero_of_notMem_tsupport hnot
    exact hx (by simp only [hz, PiLp.zero_apply])
  have hDc (j) (x) : fderiv ℝ (fun y => φ y j) x w = (fderiv ℝ φ x w) j := by
    have h := ((pr j).hasFDerivAt.comp x (hφ.differentiable one_ne_zero x).hasFDerivAt).fderiv
    exact congrArg (fun L => L w) h
  have hp2 (j) : MemLp (fun x => φ x j) 2 volume := (hc j).continuous.memLp_of_hasCompactSupport (hcs j)
  have hdp2 (j) : MemLp (fun x => (fderiv ℝ φ x w) j) 2 volume := by
    simp_rw [← hDc]
    exact (((hc j).continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcs j).fderiv_apply ℝ w)
  have hiL (j) : Integrable (fun x => g x j * φ x j) := (memLp_cell_component hg j).integrable_mul (hp2 j)
  have hiR (j) : Integrable (fun x => u x j * (fderiv ℝ φ x w) j) :=
    (memLp_cell_component hu j).integrable_mul (hdp2 j)
  have hinner (v z : OAI.Analysis.PDE.Variational.CellVectors m) : inner ℝ v z = ∑ j, v j * z j := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ (f := fun j x => g x j * φ x j) (fun j _ => hiL j),
    integral_finsetSum Finset.univ (f := fun j x => u x j * (fderiv ℝ φ x w) j)
      (fun j _ => hiR j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [hDc] using (hd j).scalar_identity volume (fun x => φ x j) (hc j) (hcs j) (hcsub j)

end OAI.Analysis.PDE.Weak
