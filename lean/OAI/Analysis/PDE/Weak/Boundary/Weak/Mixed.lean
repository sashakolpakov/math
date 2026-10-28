import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient
import OAI.Analysis.PDE.Weak.Elliptic.LocalDerivative
import OAI.Analysis.PDE.Dirichlet.Derivative

/-! Componentwise distributional derivatives and symmetry of mixed
derivatives of the actual H¹ gradient. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem HasWeakDirectionalDerivativeOn.component
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    {u g : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hd : HasWeakDirectionalDerivativeOn volume Ω v u g)
    (j : Fin (m + 1)) (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω) :
    (∫ x, g x j * φ x) = -(∫ x, u x j * fderiv ℝ φ x v) := by
  have ht : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := hφ.smul contDiff_const
  have hts : HasCompactSupport (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := by
    change HasCompactSupport ((fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ)) ∘ φ)
    apply hs.comp_left
    simp
  have hsub : tsupport (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) ⊆ Ω := by
    apply Subset.trans (b := tsupport φ) _ hΩ
    change tsupport (fun x => φ x • EuclideanSpace.single j (1 : ℝ)) ⊆ tsupport φ
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    have hz := image_eq_zero_of_notMem_tsupport hnot
    exact hx (by simp only [hz, zero_smul])
  have he := hd (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) ht hts hsub
  have hf (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      fderiv ℝ (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) x v =
        OAI.Analysis.PDE.Variational.coordinateTestVector j (fun x => fderiv ℝ φ x v) x := by
    have h := ((hφ.differentiable (by norm_num) x).hasFDerivAt.smul_const
      (EuclideanSpace.single j (1 : ℝ))).fderiv
    exact congrArg (fun L => L v) h
  have hi (w : OAI.Analysis.PDE.Variational.CellVectors m) (ψ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      inner ℝ w (OAI.Analysis.PDE.Variational.coordinateTestVector j ψ x) = w j * ψ x := by
    rw [real_inner_comm, OAI.Analysis.PDE.Variational.inner_coordinateTestVector, mul_comm]
  simpa only [hf, hi] using he

theorem H1Zero.mixed_weak_pairing {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (i j : Fin (m + 1))
    (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, p.2 x j * fderiv ℝ φ x (Pi.single i 1)) =
      ∫ x, p.2 x i * fderiv ℝ φ x (Pi.single j 1) := by
  have hi : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hφ (by norm_num) _
  have hj : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (Pi.single j 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hφ (by norm_num) _
  rw [OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp j _ hi (hs.fderiv_apply ℝ _),
    OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp i _ hj (hs.fderiv_apply ℝ _)]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  exact congrArg (fun t => p.1 x * t)
    (OAI.Analysis.PDE.Dirichlet.directionalDerivative_comm hφ (Pi.single j 1) (Pi.single i 1) x)

end OAI.Analysis.PDE.Weak
