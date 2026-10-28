import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelUnitValues

/-! # Kernel Unit Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelUnitValues

noncomputable section

/-! Exact neutral-frame values on the original scalar-kernel presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)

omit [GrpObj Z] [IsMonHom φ] in
/-- The canonical scalar-cover frame is the actual transported target unit frame. -/
theorem frame_eq {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (c : T ⟶ A ⊗ A)
    (hc : l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) = c ≫ snd A A)
    (hz : (c ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n)) ≫ snd A A = 1) :
    (PullbackKernelFrames.frames φ P Dv n).frame l c hc =
      Pulled.LineSection.transportFrame (𝟙 A ⊗ₘ (𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
        c (c ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n)) rfl
        ((Poincare.TransverseFrames.sourceVertical φ P Dv).unitFrame (c ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n)) hz) := by
  have hk : (c ≫ snd A A) ≫ (((𝟙 A) ^ n) ≫ 𝟙 A) = 1 := by
    rw [Category.comp_id, ← hc, Category.assoc, Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  let l' := (Kernel.Scheme.kernelPointsEquiv (((𝟙 A) ^ n) ≫ 𝟙 A) T).symm ⟨c ≫ snd A A, hk⟩
  have hl' : l' ≫ Kernel.Scheme.kernelInclusion (((𝟙 A) ^ n) ≫ 𝟙 A) = c ≫ snd A A :=
    Limits.pullback.lift_fst _ _ _
  unfold PullbackKernelFrames.frames
  rw [Pulled.KernelUnitValues.congr_quotient_frame _ _ _ _ _ _ l' l c hl' hc]
  exact Pulled.KernelUnitValues.vertical_frame (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
    (Poincare.TransverseFrames.sourceVertical φ P Dv) l' c hl' hz

omit [GrpObj Z] [IsMonHom φ] in
/-- The same frame is computed at any specified neutral image point. -/
theorem frame_eq_to {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (c : T ⟶ A ⊗ A)
    (hc : l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) = c ≫ snd A A)
    (d : T ⟶ A ⊗ A) (hd : c ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = d) (hz : d ≫ snd A A = 1) :
    (PullbackKernelFrames.frames φ P Dv n).frame l c hc =
      Pulled.LineSection.transportFrame (𝟙 A ⊗ₘ (𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
        c d hd ((Poincare.TransverseFrames.sourceVertical φ P Dv).unitFrame d hz) := by
  subst d
  exact frame_eq φ P Dv n l c hc hz

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelUnitValues
