import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalTransformation
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Total Extension Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionTransformation.FiniteTotalExtensionTransformation

noncomputable section

/-! The finite total comparison in integer degrees is natural in additive coefficient transformations. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (a : F ⟶ G)

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

theorem naturality (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    HomologicalComplex.extendMap (total.map (TotalTransformation.FiniteTotalTransformation.bicomplexMap a K) (.up ℕ))
        ComplexShape.embeddingUpNat ≫ (TotalIso.FiniteTotalExtension.iso G K).hom =
      (TotalIso.FiniteTotalExtension.iso F K).hom ≫
        (NatTrans.mapHomologicalComplex a (.up ℤ)).app ((K.total (.up ℕ)).extend ComplexShape.embeddingUpNat) := by
  let t := total.map (TotalTransformation.FiniteTotalTransformation.bicomplexMap a K) (.up ℕ)
  let b := (NatTrans.mapHomologicalComplex a (.up ℕ)).app (K.total (.up ℕ))
  have h₁ := (HomologicalComplex.extendMap_comp t (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G K).hom
    ComplexShape.embeddingUpNat).symm.trans
      ((congrArg (fun k => HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
        (TotalTransformation.FiniteTotalTransformation.naturality a K)).trans
          (HomologicalComplex.extendMap_comp (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom b
            ComplexShape.embeddingUpNat))
  have h₂ := Section.Hypercohomology.SectionHypercohomology.inverse_square
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (K.total (.up ℕ)))
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G ComplexShape.embeddingUpNat (K.total (.up ℕ))) _ _
    (ComplexExtensionNaturality.ComplexExtensionTransformation.naturality a ComplexShape.embeddingUpNat (K.total (.up ℕ)))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionTransformation.FiniteTotalExtensionTransformation
