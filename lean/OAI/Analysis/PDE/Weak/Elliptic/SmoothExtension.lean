import OAI.Analysis.PDE.Weak.Elliptic.CoefficientExtension
import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

theorem ellipticExtension_smoothBounded {m : ℕ}
    {A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m}
    {θ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hA : ContDiff ℝ ∞ A) (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ)
    (lam : ℝ) : SmoothBounded (ellipticExtension A θ lam) := by
  let : NormedAddCommGroup (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    ContinuousLinearMap.toNormedSpace
  let C := lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m)
  let B : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m := fun x ↦ θ x • (A x - C)
  have hB : ContDiff ℝ ∞ B := hθ.smul (hA.sub contDiff_const)
  have hBs : HasCompactSupport B := hs.smul_right
  have heq : ellipticExtension A θ lam = (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ C) + B := by
    funext x
    change θ x • A x + (1 - θ x) • (lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m)) =
      C + θ x • (A x - C)
    change θ x • A x + (1 - θ x) • C = C + θ x • (A x - C)
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact (smoothBounded_const (m := m) C).add (smoothBounded_of_hasCompactSupport hB hBs)

end OAI.Analysis.PDE.Weak
