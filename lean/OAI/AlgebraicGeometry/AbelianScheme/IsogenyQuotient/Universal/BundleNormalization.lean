import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

/-! # Bundle Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction

noncomputable section

/-! Universal global functions give unique normalized line-bundle
comparisons on arbitrary parameters, and descend equal relative Picard classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem universal_familyBaseChangeSection_bijective
    {X S : Scheme.{u}} (p : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions (Over.mk p)) (T : Over S) :
    Function.Bijective ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left.appTop := by
  have : IsIso (pullback.fst T.hom p).appTop :=
    hΓ.isIso_of_isPullback (pullback.snd T.hom p) (pullback.fst T.hom p) T.hom
      (IsPullback.of_hasPullback T.hom p).flip
  have : IsIso ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left.appTop :=
    AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (pullback.fst T.hom p)
      ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left (AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection_fst p σ hσ T)
  exact ConcreteCategory.bijective_of_isIso _

theorem universal_existsUnique_bundleIso_with_section_fiber
    {X S : Scheme.{u}} (p : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions (Over.mk p))
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hLM : Nonempty (L.sheaf ≅ M.sheaf))
    (b : (L.pullback σ).sheaf ≅ (M.pullback σ).sheaf) :
    ∃! e : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback σ).map e.hom = b.hom := by
  have : IsIso p.appTop := hΓ.self
  have : IsIso σ.appTop := AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants.section_globalFunctions_isIso p σ hσ
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.existsUnique_iso_with_pullback _ (ConcreteCategory.bijective_of_isIso _) L M hLM b

theorem universal_bundleIso_of_relativePicard_eq
    {S : Scheme.{u}} (P T : Over S) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions P)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).obj T))
    (y : T.left ⟶ (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).obj T)
    (hy : y ≫ pullback.fst T.hom P.hom = 𝟙 _)
    (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard P).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard P).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have hF := hΓ.of_isPullback (pullback.snd T.hom P.hom) (pullback.fst T.hom P.hom) T.hom
    (IsPullback.of_hasPullback T.hom P.hom).flip
  exact AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq P T L M y hy b
    (universal_familyBaseChangeSection_bijective (pullback.fst T.hom P.hom) y hy hF) h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction
