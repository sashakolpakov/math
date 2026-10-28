import OAI.Analysis.PDE.Green.CellFiber
import OAI.Analysis.PDE.Energy.CurrentInequality

/-! The combined determinant/current fiber energy and its elementary regularity. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

def combinedEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) : ℝ :=
  -u x * (A x 0 0).re + lam⁻¹ * spatialPencilEnergyDensity e B u x

def setFiberCombinedEnergy {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s))
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : ℝ :=
  ∫ y in (fiberEmbedding n s z) ⁻¹' S, combinedEnergyDensity e lam A B u (fiberEmbedding n s z y)

theorem continuous_quaternion_real : Continuous (fun q : Quaternion ℝ => q.re) := by
  let L : Quaternion ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun q => q.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.continuous_of_finiteDimensional

theorem continuous_current_mass {n s : ℕ}
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : Continuous A) : Continuous (fun x => (A x 0 0).re) := by
  apply continuous_quaternion_real.comp
  exact (continuous_apply 0).comp ((continuous_apply 0).comp hA)

theorem continuous_current_pairing {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : Continuous A) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 3 u) :
    Continuous (fun x => OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) := by
  have hH := OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu
  change Continuous (fun x => (∑ i, ∑ j, A x i j * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x j i).re)
  apply continuous_quaternion_real.comp
  fun_prop

theorem continuous_combinedEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : Continuous A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) :
    Continuous (combinedEnergyDensity e lam A B u) :=
  (hu.continuous.neg.mul (continuous_current_mass hA)).add
    (continuous_const.mul (continuous_spatialPencilEnergyDensity e hB hu))

theorem spatial_hessian_segment_posSemidef {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (h0 : (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x).submatrix Fin.succ Fin.succ)).PosSemidef)
    (h1 : (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
      Fin.succ Fin.succ)).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
      Fin.succ Fin.succ)).PosSemidef := by
  have h := OAI.Analysis.PDE.Energy.hessian_segment e hB hu t x
  simp only [smul_eq_mul] at h
  rw [h]
  change (OAI.LinearAlgebra.Moore.complexify (t • (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
    Fin.succ Fin.succ + (1 - t) • (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x).submatrix Fin.succ Fin.succ)).PosSemidef
  rw [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact (h1.smul ht.1).add (h0.smul (sub_nonneg.mpr ht.2))

end OAI.Analysis.PDE.Green
