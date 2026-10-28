import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubicalBilinear
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Picard Bilinear -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction

noncomputable section

/-! The actual Picard-valued polarization of pullback on endomorphisms,
and its extension to the rational endomorphism algebra. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- Polarization of the actual line-bundle pullback class. -/
def algebraicEndPicardPairing (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    Endomorphisms.Construction.AlgebraicEnd A →ₗ[ℤ] Endomorphisms.Construction.AlgebraicEnd A →ₗ[ℤ] Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left) :=
  CubicalBilinear.Construction.cubicalCrossBilinear (PicardQuadratic.Construction.algebraicEndLineBundleClass A L)
    (PicardQuadratic.Construction.algebraicEndLineBundleClass_zero A L) (PicardQuadratic.Construction.algebraicEndLineBundleClass_cube A L)

theorem algebraicEndPicardPairing_apply (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndPicardPairing A L f g = PicardQuadratic.Construction.algebraicEndLineBundleClass A L (f + g) -
      PicardQuadratic.Construction.algebraicEndLineBundleClass A L f - PicardQuadratic.Construction.algebraicEndLineBundleClass A L g := rfl

theorem algebraicEndPicardPairing_symmetric (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndPicardPairing A L f g = algebraicEndPicardPairing A L g f :=
  CubicalBilinear.Construction.cubicalCrossEffect_symmetric (PicardQuadratic.Construction.algebraicEndLineBundleClass A L) f g

theorem algebraicEndPicardPairing_self (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndPicardPairing A L f f = 2 • PicardQuadratic.Construction.algebraicEndLineBundleClass A L f := by
  rw [algebraicEndPicardPairing_apply, ← two_nsmul,
    PicardQuadratic.Construction.algebraicEndLineBundleClass_nsmul A L hsym f 2]
  norm_num only [Nat.reduceMul]
  abel

/-- The Picard-valued pairing on the actual rational algebra of endomorphisms. -/
def rationalAlgebraicEndPicardPairing (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    Endomorphisms.Construction.RationalAlgebraicEnd A →ₗ[ℚ] Endomorphisms.Construction.RationalAlgebraicEnd A →ₗ[ℚ]
      TensorProduct ℤ ℚ (Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left)) :=
  LinearMap.BilinMap.baseChange ℚ (algebraicEndPicardPairing A L)

theorem rationalAlgebraicEndPicardPairing_tmul (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (r s : ℚ) (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    rationalAlgebraicEndPicardPairing A L (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) =
      (r * s) ⊗ₜ[ℤ] algebraicEndPicardPairing A L f g := rfl

theorem rationalAlgebraicEndPicardPairing_symmetric (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (x y : Endomorphisms.Construction.RationalAlgebraicEnd A) :
    rationalAlgebraicEndPicardPairing A L x y = rationalAlgebraicEndPicardPairing A L y x :=
  LinearMap.BilinMap.baseChange_isSymm (algebraicEndPicardPairing_symmetric A L) x y

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction
