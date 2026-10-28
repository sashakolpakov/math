import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.DiagonalPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison

/-! # Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A full level structure makes multiplication by its level integer unramified over every base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_formallyUnramified (level : A.FullLevel n) :
    FormallyUnramified (A.multiplication n).left := by
  have H := (A.multiplicationDifference_isPullback n).map (Over.forget S)
  have hz : IsOpenImmersion (A.torsionZeroSection n).left :=
    A.torsionZeroSection_isOpenImmersion level
  have : IsOpenImmersion (pullback.diagonal (A.multiplication n)).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hz
  exact HilbertConstruction.Over.DiagonalComparison.formallyUnramified_of_overDiagonal (A.multiplication n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
