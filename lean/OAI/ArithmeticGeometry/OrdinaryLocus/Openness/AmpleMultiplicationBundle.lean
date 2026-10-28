import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupAmpleBundle
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPowerComparison

/-! # Ample Multiplication Bundle -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleMultiplicationBundle.Construction

noncomputable section

/-! A symmetric ample bundle with the actual multiplication pullback formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem symmetricLineBundleMultiplication_universal (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hs : Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf)) (n : ℕ) :
    Nonempty ((L.pullback (Multiplication.Construction.multiplicationMap A n).left).sheaf ≅ (L.tensorPower (n ^ 2)).sheaf) := by
  obtain ⟨e⟩ := GeometricCube.Construction.symmetricLineBundleMultiplication A L.sheaf L.locallyTrivial hs n
  exact ⟨e ≪≫ (TensorPowerComparison.Construction.lineBundleTensorPowerComparison L (n ^ 2)).symm⟩

theorem exists_ample_multiplication_bundle :
    ∃ L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple ∧ ∀ n : ℕ,
      Nonempty ((L.pullback (Multiplication.Construction.multiplicationMap A n).left).sheaf ≅ (L.tensorPower (n ^ 2)).sheaf) := by
  obtain ⟨L, hL, hs⟩ := GroupAmpleBundle.Construction.exists_symmetric_ample_lineBundle A
  exact ⟨L, hL, symmetricLineBundleMultiplication_universal A L hs⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleMultiplicationBundle.Construction
