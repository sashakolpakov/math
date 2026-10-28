import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits

/-! # Multiplication Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.MultiplicationUnits

noncomputable section

/-! The two genuine Poincare products retain their common origin unit under both coordinate pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (B ⊗ Y).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst B Y) (snd B Y) L) (Dv : FiberwiseMultiplication.Multiplication (snd B Y) (fst B Y) L)

/-- Pulling both actual coordinates preserves the common origin frame of the full multiplications. -/
theorem unitFrames_eq (T : Over S)
    (hs : Dh.unitFrame (1 : T ⟶ B ⊗ Y) (MonObj.one_comp (fst B Y)) =
      Dv.unitFrame 1 (MonObj.one_comp (snd B Y))) :
    (KernelFrameIsotropy.horizontalMultiplication f g L Dh).unitFrame (1 : T ⟶ A ⊗ X) (MonObj.one_comp (fst A X)) =
      (KernelFrameIsotropy.verticalMultiplication f g L Dv).unitFrame 1 (MonObj.one_comp (snd A X)) := by
  unfold KernelFrameIsotropy.horizontalMultiplication KernelFrameIsotropy.verticalMultiplication MultiplicationPullbackSquare.multiplication
    MultiplicationFixedMap.restrictFixed MultiplicationCoordinateMap.restrictCoordinate
  dsimp only
  unfold MultiplicationPullbackSquare.imageMultiplication
  rw [AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits.Construction.multiplication_congrCoordinates_unitFrame,
    AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits.Construction.multiplication_congrCoordinates_unitFrame]
  change (Dh.unitFrame ((1 : T ⟶ A ⊗ X) ≫ (f ⊗ₘ g)) _ ≪≫
      (LineBilinear.fiberComparison (f ⊗ₘ g) L 1 (1 ≫ (f ⊗ₘ g)) rfl).symm) =
    (Dv.unitFrame ((1 : T ⟶ A ⊗ X) ≫ (f ⊗ₘ g)) _ ≪≫
      (LineBilinear.fiberComparison (f ⊗ₘ g) L 1 (1 ≫ (f ⊗ₘ g)) rfl).symm)
  have he (a : T ⟶ B ⊗ Y) (ha : a = 1) (hh : a ≫ fst B Y = 1) (hv : a ≫ snd B Y = 1) :
      Dh.unitFrame a hh = Dv.unitFrame a hv := by
    subst a
    exact hs
  rw [he _ (MonObj.one_comp (f ⊗ₘ g))]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.MultiplicationUnits
