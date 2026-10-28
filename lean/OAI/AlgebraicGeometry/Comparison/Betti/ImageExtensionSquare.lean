import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage
import OAI.AlgebraicGeometry.Comparison.Betti.ExtensionCoherence

/-! # Image Extension Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

noncomputable section

section

/-! The actual top-section coefficient map commutes with extension from nonnegative to integer degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

def additiveTopSectionsFunctor (X : TopCat.{0}) : ConstantSheafSections.ComplexSheaves X ⥤ AddCommGrpCat.{0} :=
  FlasqueBiproduct.sections (⊤ : Opens X) ⋙ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}

instance additiveTopSectionsFunctor_additive (X : TopCat.{0}) : (additiveTopSectionsFunctor X).Additive where
  map_add := by intros; rfl

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ} {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

def extendDirectImageComplexMap : K.extend (ComplexShape.embeddingUpIntGE 0) ⟶
    ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).obj (L.extend (ComplexShape.embeddingUpIntGE 0)) :=
  HomologicalComplex.extendMap α (ComplexShape.embeddingUpIntGE 0) ≫
    (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafDirectImage f) (ComplexShape.embeddingUpIntGE 0) L).inv

def natTopSectionsPullback :=
  Sheaf.CechPullbackTotal.topGlobalSectionsPullback f (Godement.AdditiveImage.additiveDirectImageComplexMap f α)

def topSectionsExtensionIso (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ) :
    ImageAdjointNaturality.integerAdditiveTopGlobalComplex (K.extend (ComplexShape.embeddingUpIntGE 0)) ≅
      (((additiveTopSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K).extend
        (ComplexShape.embeddingUpIntGE 0) :=
  Complex.Extension.mapExtendIso (additiveTopSectionsFunctor X) (ComplexShape.embeddingUpIntGE 0) K

theorem topSectionsExtension_option (o : Option ℕ) :
    (additiveTopSectionsFunctor X).map
        (HomologicalComplex.extend.mapX α o ≫ (Complex.Extension.mapXIso (TopologicalSheafPullback.sheafDirectImage f) L o).inv) ≫
      (Complex.Extension.mapXIso (additiveTopSectionsFunctor Y) L o).hom =
    (Complex.Extension.mapXIso (additiveTopSectionsFunctor X) K o).hom ≫
      HomologicalComplex.extend.mapX (natTopSectionsPullback f α) o := by
  cases o with
  | none =>
    exact ((additiveTopSectionsFunctor X).map_isZero (isZero_zero _)).eq_of_src _ _
  | some n =>
    change (additiveTopSectionsFunctor X).map (α.f n ≫ 𝟙 _) ≫ 𝟙 _ =
      𝟙 _ ≫ (natTopSectionsPullback f α).f n
    rw [Category.comp_id, Category.comp_id, Category.id_comp]
    rfl

theorem integerTopGlobalSectionsPullback_extend :
    ImageAdjointNaturality.integerTopGlobalSectionsPullback f (extendDirectImageComplexMap f α) ≫
        (topSectionsExtensionIso L).hom =
      (topSectionsExtensionIso K).hom ≫
        HomologicalComplex.extendMap (natTopSectionsPullback f α) (ComplexShape.embeddingUpIntGE 0) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact topSectionsExtension_option f α ((ComplexShape.embeddingUpIntGE 0).r n)

end

/-! The original coefficient square is retained by canonical integer extension across direct image. -/

open _root_.CategoryTheory

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {K K' : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ} {L L' : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)
  (γ : K' ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L')
  (e : K ⟶ K') (d : L ⟶ L')
  (h : e ≫ γ = α ≫ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map d)

include h in
theorem extendDirectImageComplexMap_square :
    HomologicalComplex.extendMap e (ComplexShape.embeddingUpIntGE 0) ≫ extendDirectImageComplexMap f γ =
      extendDirectImageComplexMap f α ≫
        ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap d (ComplexShape.embeddingUpIntGE 0)) := by
  let E := (ComplexShape.embeddingUpIntGE 0).extendFunctor (ConstantSheafSections.ComplexSheaves X)
  let j := (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafDirectImage f) (ComplexShape.embeddingUpIntGE 0) L).inv
  let j' := (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafDirectImage f) (ComplexShape.embeddingUpIntGE 0) L').inv
  let u := ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map d
  let v := ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap d (ComplexShape.embeddingUpIntGE 0))
  have hn : j ≫ v = E.map u ≫ j' :=
    ExtensionCoherence.Complex.mapExtendIso_inv_naturality (TopologicalSheafPullback.sheafDirectImage f) (ComplexShape.embeddingUpIntGE 0) d
  change E.map e ≫ (E.map γ ≫ j') = (E.map α ≫ j) ≫ v
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ j') (E.map_comp e γ).symm).trans
      ((congrArg (fun z => E.map z ≫ j') h).trans
        ((congrArg (· ≫ j') (E.map_comp α u)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (E.map α ≫ ·) hn.symm).trans (Category.assoc _ _ _).symm)))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare
