import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

/-! # Pulled Multiplication Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits.Construction

noncomputable section

/-! The common origin unit of two genuine multiplications remains
common after pullback in the first coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

set_option backward.isDefEq.respectTransparency false in
theorem sourceMultiplications_unit_zero
    {S : Scheme.{u}} {A Z X : Over S} [GrpObj A] [GrpObj Z] [GrpObj X]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ X).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z X) (snd Z X) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z X) (fst Z X) P)
    (T : Over S)
    (hs : Dh.unitFrame (1 : T ⟶ Z ⊗ X) (MonObj.one_comp (fst Z X)) =
      Dv.unitFrame 1 (MonObj.one_comp (snd Z X))) :
    (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh).unitFrame (1 : T ⟶ A ⊗ X)
      (MonObj.one_comp (fst A X)) =
    (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv).unitFrame 1 (MonObj.one_comp (snd A X)) := by
  change (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.imageMultiplication φ P Dh).unitFrame 1 _ =
    (Picard.PoincareBundle.Poincare.TransverseFrames.imageVertical φ P Dv).unitFrame 1 _
  rw [Picard.PoincareBundle.Pulled.KernelFrames.Poincare.imageMultiplication, Picard.PoincareBundle.Poincare.TransverseFrames.imageVertical,
    SymmetricMultiplicationUnits.Construction.multiplication_congrCoordinates_unitFrame, SymmetricMultiplicationUnits.Construction.multiplication_congrCoordinates_unitFrame]
  change (Dh.unitFrame ((1 : T ⟶ A ⊗ X) ≫ (φ ⊗ₘ 𝟙 X)) _ ≪≫
      (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (φ ⊗ₘ 𝟙 X) P 1 (1 ≫ (φ ⊗ₘ 𝟙 X)) rfl).symm) =
    (Dv.unitFrame ((1 : T ⟶ A ⊗ X) ≫ (φ ⊗ₘ 𝟙 X)) _ ≪≫
      (Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (φ ⊗ₘ 𝟙 X) P 1 (1 ≫ (φ ⊗ₘ 𝟙 X)) rfl).symm)
  have he (a : T ⟶ Z ⊗ X) (ha : a = 1) (hh : a ≫ fst Z X = 1) (hv : a ≫ snd Z X = 1) :
      Dh.unitFrame a hh = Dv.unitFrame a hv := by
    subst a
    exact hs
  rw [he _ (MonObj.one_comp (φ ⊗ₘ 𝟙 X))]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits.Construction
