import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericHomogeneityNaturality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DoubleFamilyIsoDescent

/-! # Generic Finite Homogeneity Descent -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiniteHomogeneityDescent.Geometric

noncomputable section

/-! Original all-test homogeneity descends to a finitely generated
parameter subalgebra over any base with universal global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericHomogeneityNaturality.Geometric.GenericHomogeneity

variable {k B R : Type} [CommRing k] [CommRing B] [CommRing R]
    [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

theorem exists_fg_homogeneous_parameter_line {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B ⊗ A.scheme).left)
    (hR : A.IsHomogeneousPicardClass (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R ⊗ₘ 𝟙 A.scheme).left))) :
    ∃ T : Subalgebra B R, T.FG ∧
      A.IsHomogeneousPicardClass (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B T ⊗ₘ 𝟙 A.scheme).left)) := by
  let L := GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalTranslationLine A Q
  let N := GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalParameterLine A Q
  obtain ⟨e⟩ := (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.homogeneous_iff_universal_normalized_lineIso A _ hA).mp hR
  obtain ⟨eL⟩ := Quotient.exact
    (GenericHomogeneityNaturality.Geometric.GenericHomogeneity.normalizedUniversalTranslationLine_class_naturality A Q (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R))
  obtain ⟨eN⟩ := Quotient.exact
    (GenericHomogeneityNaturality.Geometric.GenericHomogeneity.normalizedUniversalParameterLine_class_naturality A Q (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R))
  obtain ⟨T, hT, ⟨d⟩⟩ := DoubleFamilyIsoDescent.Geometric.exists_fg_double_family_lineIso k B R A.scheme A.scheme L N
    (eL ≪≫ e ≪≫ eN.symm)
  refine ⟨T, hT, (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.homogeneous_iff_universal_normalized_lineIso A _ hA).mpr ?_⟩
  obtain ⟨dL⟩ := Quotient.exact
    (GenericHomogeneityNaturality.Geometric.GenericHomogeneity.normalizedUniversalTranslationLine_class_naturality A Q (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B T))
  obtain ⟨dN⟩ := Quotient.exact
    (GenericHomogeneityNaturality.Geometric.GenericHomogeneity.normalizedUniversalParameterLine_class_naturality A Q (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B T))
  exact ⟨dL.symm ≪≫ d ≪≫ dN⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiniteHomogeneityDescent.Geometric
