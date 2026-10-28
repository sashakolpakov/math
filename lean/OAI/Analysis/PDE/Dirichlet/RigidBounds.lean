import OAI.Analysis.PDE.Dirichlet.RigidEquation
import OAI.Analysis.PDE.Dirichlet.LocalBarrier

open Filter Set
open scoped Topology ComplexOrder Matrix

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem affineDerivative_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (e : E) (A : E →L[ℝ] E) :
    affineDerivative (fun y ↦ f y + g y) e A =
      fun y ↦ affineDerivative f e A y + affineDerivative g e A y := by
  funext x
  have hd : fderiv ℝ (fun y ↦ f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv
  unfold affineDerivative
  rw [hd]
  rfl

theorem mooreDifferential_abs_le_identity {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (C : ℝ)
    (hplus : (OAI.LinearAlgebra.Moore.complexify (D + C • 1)).PosSemidef)
    (hminus : (OAI.LinearAlgebra.Moore.complexify ((-1 : ℝ) • D + C • 1)).PosSemidef) :
    |OAI.LinearAlgebra.Moore.mooreDifferential n A D| ≤ C * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
  have hp := OAI.LinearAlgebra.Moore.mooreDifferential_nonneg_of_posDef A (D + C • 1) hA hplus
  have hm := OAI.LinearAlgebra.Moore.mooreDifferential_nonneg_of_posDef A ((-1 : ℝ) • D + C • 1) hA hminus
  simp only [OAI.LinearAlgebra.Moore.mooreDifferential_add, OAI.LinearAlgebra.Moore.mooreDifferential_smul] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exact rigid-motion equation after subtracting the prescribed background. -/
theorem mooreLinearization_rigid_remainder {n : ℕ}
    {B₀ u F : CoordinateSpace n 4 → ℝ}
    (hB₀ : ContDiff ℝ 3 B₀) (hu : ContDiff ℝ 3 u)
    (e : CoordinateSpace n 4) (R : Matrix (Fin n) (Fin n) Q) (hR : Rᴴ = -R)
    {x : CoordinateSpace n 4} (hF : DifferentiableAt ℝ F x)
    (heq : (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y))
      =ᶠ[𝓝 x] F) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
      (affineDerivative u e (realMatrixAction (realRepresentation R))) x =
      affineDerivative F e (realMatrixAction (realRepresentation R)) x -
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
        (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) x := by
  have hid := mooreLinearization_rigid_eq (hB₀.add hu) e R hR hF heq
  rw [affineDerivative_add (hB₀.differentiable (by norm_num))
    (hu.differentiable (by norm_num))] at hid
  have hb : ContDiff ℝ 2 (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) :=
    contDiff_affineDerivative hB₀ (by norm_num) _ _
  have hh : ContDiff ℝ 2 (affineDerivative u e (realMatrixAction (realRepresentation R))) :=
    contDiff_affineDerivative hu (by norm_num) _ _
  have hadd := mooreLinearization_add_smul
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z)) hb hh 1 x
  simp only [one_smul, one_mul] at hadd
  rw [hadd] at hid
  linarith

/-- A fixed-background Hessian bound and the data gradient bound control the
rigid-motion forcing by the positive trace of the actual linearization. -/
theorem mooreLinearization_rigid_forcing {n : ℕ}
    {B₀ u F : CoordinateSpace n 4 → ℝ}
    (hB₀ : ContDiff ℝ 3 B₀) (hu : ContDiff ℝ 3 u)
    (e : CoordinateSpace n 4) (R : Matrix (Fin n) (Fin n) Q) (hR : Rᴴ = -R)
    {x : CoordinateSpace n 4} (hF : DifferentiableAt ℝ F x)
    (heq : (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y))
      =ᶠ[𝓝 x] F) {κ L K : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (hA : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x)).PosDef)
    (htrace : κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1)
    (hFbound : |affineDerivative F e (realMatrixAction (realRepresentation R)) x| ≤ L)
    (hplus : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) x + K • 1)).PosSemidef)
    (hminus : (OAI.LinearAlgebra.Moore.complexify ((-1 : ℝ) • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) x + K • 1)).PosSemidef) :
    |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
      (affineDerivative u e (realMatrixAction (realRepresentation R))) x| ≤
      (L / κ + K) * OAI.LinearAlgebra.Moore.mooreDifferential n
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1 := by
  let A := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x
  let D := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
    (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) x
  have hDb : |OAI.LinearAlgebra.Moore.mooreDifferential n A D| ≤ K * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 :=
    mooreDifferential_abs_le_identity A D hA K hplus hminus
  have hLb : L ≤ (L / κ) * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
    have h := mul_le_mul_of_nonneg_left htrace (div_nonneg hL hκ.le)
    rwa [div_mul_cancel₀ _ hκ.ne'] at h
  rw [mooreLinearization_rigid_remainder hB₀ hu e R hR hF heq]
  calc
    _ ≤ |affineDerivative F e (realMatrixAction (realRepresentation R)) x| +
        |OAI.LinearAlgebra.Moore.mooreDifferential n A D| := by
      simpa only [A, D, mooreLinearization, sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (affineDerivative F e (realMatrixAction (realRepresentation R)) x)
          0 (OAI.LinearAlgebra.Moore.mooreDifferential n A D))
    _ ≤ L + K * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := add_le_add hFbound hDb
    _ ≤ (L / κ) * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 + K * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 :=
      add_le_add hLb le_rfl
    _ = _ := by ring

end OAI.Analysis.PDE.Dirichlet
