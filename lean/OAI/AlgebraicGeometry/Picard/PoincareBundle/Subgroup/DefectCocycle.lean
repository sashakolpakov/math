import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCoordinates

/-! # Defect Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle

noncomputable section

/-! The actual subgroup translation defect is a regular two-cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem defect_eq_parameter {T : Over (Spec (.of k))} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z)
    (hc : a * b = c) :
    TranslationDefect.defect i L t x y z a b c hx hy hz = DefectParameters.value i L t a b :=
  (DefectCoordinates.value_eq_defect i L t x y z a b c hx hy hz hc).symm.trans (DefectParameters.defect_eq_value i L t a b x)

/-- This law follows from associativity of sheaf-isomorphism composition and properness.
No cocycle identity is supplied as a hypothesis. -/
theorem cocycle {T : Over (Spec (.of k))} (a b c : T ⟶ H) :
    DefectParameters.value i L t (a * b) c * DefectParameters.value i L t a b =
      DefectParameters.value i L t a (b * c) * DefectParameters.value i L t b c := by
  let x : T ⟶ A := 1
  let y := (a ≫ i) * x
  let z := ((a * b) ≫ i) * x
  let w := (((a * b) * c) ≫ i) * x
  have h₀₁ : (a ≫ i) * x = y := rfl
  have h₁₂ : (b ≫ i) * y = z := ProductDefect.translate_mul i a b x
  have h₂₃ : (c ≫ i) * z = w := ProductDefect.translate_mul i (a * b) c x
  have h₀₂ : ((a * b) ≫ i) * x = z := rfl
  have h₀₃ : (((a * b) * c) ≫ i) * x = w := rfl
  have h₁₃ : ((b * c) ≫ i) * y = w :=
    (ProductDefect.translate_mul i a (b * c) x).trans
      (congrArg (fun d => (d ≫ i) * x) (mul_assoc a b c).symm)
  have h : TranslationDefect.defect i L t x y z a b (a * b) h₀₁ h₁₂ h₀₂ *
      TranslationDefect.defect i L t x z w (a * b) c ((a * b) * c) h₀₂ h₂₃ h₀₃ =
      TranslationDefect.defect i L t y z w b c (b * c) h₁₂ h₂₃ h₁₃ *
        TranslationDefect.defect i L t x y w a (b * c) ((a * b) * c) h₀₁ h₁₃ h₀₃ :=
    IsomorphismDefectCocycle.cocycle (FiberIsomorphismRatios.fiberLine L x) (FiberIsomorphismRatios.fiberLine L y)
      (TranslationFibers.transportIso i L t x y a h₀₁) (TranslationFibers.transportIso i L t y z b h₁₂)
      (TranslationFibers.transportIso i L t z w c h₂₃) (TranslationFibers.transportIso i L t x z (a * b) h₀₂)
      (TranslationFibers.transportIso i L t y w (b * c) h₁₃) (TranslationFibers.transportIso i L t x w ((a * b) * c) h₀₃)
  have h₁ := defect_eq_parameter i L t x y z a b (a * b) h₀₁ h₁₂ h₀₂ rfl
  have h₂ := defect_eq_parameter i L t x z w (a * b) c ((a * b) * c) h₀₂ h₂₃ h₀₃ rfl
  have h₃ := defect_eq_parameter i L t y z w b c (b * c) h₁₂ h₂₃ h₁₃ rfl
  have h₄ := defect_eq_parameter i L t x y w a (b * c) ((a * b) * c) h₀₁ h₁₃ h₀₃
    (mul_assoc a b c).symm
  have hv := (congrArg₂ (· * ·) h₁ h₂).symm.trans (h.trans (congrArg₂ (· * ·) h₃ h₄))
  simpa only [mul_comm] using hv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle
