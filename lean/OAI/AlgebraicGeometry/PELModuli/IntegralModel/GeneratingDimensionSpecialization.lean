import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DimensionSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness

/-! # Generating Dimension Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingDimensionSpecialization

noncomputable section

/-! Simultaneous arithmetic specialization of generation and dimension
for a smooth proper group family with fixed connected source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem arithmetic_generating_equal_dimension_specialization
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    (S : Over (Spec (.of K))) [LocallyOfFiniteType S.hom]
    (X A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth A.hom] [IsProper A.hom] (a : X ⟶ A)
    (c : Spec (.of ℂ) ⟶ S.left) [IsDominant c] (n : ℕ)
    (hn : Surjective ((Over.pullback c).map (Words.DifferenceWords.map a n)).left)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : Base.ArithmeticBaseExtension K κ) (p : Over.mk D.fieldExtension ⟶ S),
      D.denominator = N ∧
      Surjective ((Over.pullback p.left).map (Words.DifferenceWords.map a n)).left ∧
      topologicalKrullDim ((Over.pullback c).obj A).left =
        topologicalKrullDim ((Over.pullback
          (Spec.map (CommRingCat.ofHom D.embedding) ≫ p.left)).obj A).left := by
  have : Surjective (Words.DifferenceWords.map a n).left :=
    Specialization.surjective_of_dominant_base_change c (Words.DifferenceWords.map a n) hn
  have : GeometricallyConnected A.hom := GeneratingFiberConnectedness.DifferenceWords.target_geometricallyConnected a n
  obtain ⟨D, p, hD, hd⟩ := Arithmetic.DimensionSpecialization.arithmetic_equal_dimension_specialization κ S A c N hN
  have hp : Surjective ((Over.pullback p.left).map (Words.DifferenceWords.map a n)).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square p.left (Words.DifferenceWords.map a n))
      (inferInstanceAs (Surjective (Words.DifferenceWords.map a n).left))
  exact ⟨D, p, hD, hp, hd⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingDimensionSpecialization
