import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleMultiplicationBundle
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GlobalSectionDimension

/-! # Multiplication Hilbert Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertSections.Construction

noncomputable section

/-! Multiplication converts the pushforward Hilbert function to the rescaled line-bundle Hilbert function. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem symmetricLineBundleMultiplication_power (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hs : Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf)) (m n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (Multiplication.Construction.multiplicationMap A m).left).obj (L.tensorPower n).sheaf ≅
      (L.tensorPower (n * m ^ 2)).sheaf) := by
  have hsym : PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left
      (PicardEq.Construction.lineBundleClass L.sheaf L.locallyTrivial) = PicardEq.Construction.lineBundleClass L.sheaf L.locallyTrivial :=
    (PicardEq.Construction.lineBundleClass_eq_iff _ L.locallyTrivial).mpr hs
  apply (PicardEq.Construction.lineBundleClass_eq_iff
    (LineBundle.Construction.isLineBundle_pullback _ _ (L.tensorPower n).locallyTrivial)
    (L.tensorPower (n * m ^ 2)).locallyTrivial).mp
  change PicardPullback.Construction.picardPullback (Multiplication.Construction.multiplicationMap A m).left
    (PicardEq.Construction.lineBundleClass (L.tensorPower n).sheaf (L.tensorPower n).locallyTrivial) = _
  rw [TensorPowerComparison.Construction.lineBundleClass_universalTensorPower, TensorPowerComparison.Construction.lineBundleClass_universalTensorPower,
    map_nsmul, GeometricCube.Construction.picardMultiplication A _ hsym, smul_smul]

theorem multiplication_pushforward_sections_finrank (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hs : Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf)) (m n : ℕ) :
    Module.finrank Γ(Spec (.of K), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj
        (SheafTensor.Construction.sheafTensor ((Scheme.Modules.pushforward (Multiplication.Construction.multiplicationMap A m).left).obj
          (LineBundle.Construction.structureSheafModule A.left)) (L.tensorPower n).sheaf)) =
    Module.finrank Γ(Spec (.of K), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj (L.tensorPower (n * m ^ 2)).sheaf) := by
  let f := (Multiplication.Construction.multiplicationMap A m).left
  let M := (L.tensorPower n).sheaf
  obtain ⟨e⟩ := symmetricLineBundleMultiplication_power A L hs m n
  let eT : SheafTensor.Construction.sheafTensor (LineBundle.Construction.structureSheafModule A.left) ((Scheme.Modules.pullback f).obj M) ≅
      (L.tensorPower (n * m ^ 2)).sheaf := SheafTensor.Construction.sheafTensorUnitLeft _ ≪≫ e
  have h₁ := (PushforwardSections.Construction.lineBundleProjectionSectionsEquiv f A.hom (L.tensorPower n)
    (LineBundle.Construction.structureSheafModule A.left)).finrank_eq
  have h₂ := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ A.hom)).mapIso eT).toLinearEquiv.finrank_eq
  exact h₁.trans (h₂.trans
    (GlobalSectionDimension.Construction.baseGlobalSections_finrank_congr (Over.w (Multiplication.Construction.multiplicationMap A m)) _))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertSections.Construction
