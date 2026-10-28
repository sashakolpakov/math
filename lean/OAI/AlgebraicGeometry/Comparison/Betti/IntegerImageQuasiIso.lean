import OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

/-! # Integer Image Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegerImageQuasiIso

noncomputable section

/-! A quasi-isomorphism of the original nonnegative section maps remains a quasi-isomorphism after canonical integer extension. -/

open _root_.CategoryTheory

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ} {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

theorem integerTopGlobalSectionsPullback_extend_quasiIso
    (hα : QuasiIso (ImageExtensionSquare.natTopSectionsPullback f α)) :
    QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback f (ImageExtensionSquare.extendDirectImageComplexMap f α)) := by
  have he : QuasiIso (HomologicalComplex.extendMap (ImageExtensionSquare.natTopSectionsPullback f α)
      (ComplexShape.embeddingUpIntGE 0)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr hα
  have hc : QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback f (ImageExtensionSquare.extendDirectImageComplexMap f α) ≫
      (ImageExtensionSquare.topSectionsExtensionIso L).hom) := by
    rw [ImageExtensionSquare.integerTopGlobalSectionsPullback_extend]
    exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso (ImageExtensionSquare.topSectionsExtensionIso K).hom) (hφ' := he)
  exact quasiIso_of_comp_right _ _
    (hφ := quasiIso_of_isIso (ImageExtensionSquare.topSectionsExtensionIso L).hom) (hφφ' := hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegerImageQuasiIso
