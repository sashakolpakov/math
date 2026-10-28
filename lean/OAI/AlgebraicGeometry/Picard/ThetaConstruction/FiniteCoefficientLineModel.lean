import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DoubleFamilyIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

/-! # Finite Coefficient Line Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiniteCoefficientLineModel.Geometric

noncomputable section

/-! Actual finite-coefficient models retain their original tensor
family and exact original parameter pullback, over any Noetherian ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

variable (k R : Type) [CommRing k] [CommRing R] [Algebra k R]

theorem finiteCoefficientFamilyCone_projection (X : Over (Spec (.of k))) (s : Finset R) :
    (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone k R X).π.app (.op s) =
      (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s) R ▷ X).left := by
  have h : AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecMap k (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s).val =
      DoubleFamilyIsoDescent.Geometric.algebraParameterMap k (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s) R := by
    apply Over.OverMorphism.ext
    rfl
  exact congrArg (fun f => (f ▷ X).left) h

theorem exists_finiteType_original_line_model [IsNoetherianRing k]
    (X : Over (Spec (.of k))) [IsProper X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R ⊗ X).left) :
    ∃ (s : Finset R)
      (K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s) ⊗ X).left),
      Nonempty ((K.pullback
        (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s) R ▷ X).left).sheaf ≅ L.sheaf) := by
  obtain ⟨s, K, hK⟩ := AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent.exists_finite_coefficient_line_model k R X L
  exact ⟨s, K, (congrArg (fun f => Nonempty ((K.pullback f).sheaf ≅ L.sheaf))
    (finiteCoefficientFamilyCone_projection k R X s)).mp hK⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiniteCoefficientLineModel.Geometric
