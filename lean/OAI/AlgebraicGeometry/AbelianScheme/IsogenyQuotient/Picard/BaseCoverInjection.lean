import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat
import Mathlib.CategoryTheory.Sites.LocallySurjective
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Base Cover Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.BaseCoverInjection.Construction

noncomputable section

/-! A faithfully flat quasi-compact change of the original base detects
equality of all Picard sheaf sections, including classes represented
only locally by actual line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {S Y : Scheme.{0}} (p : Y ⟶ S)

def baseCoverRestrictionMap (F : (Over S)ᵒᵖ ⥤ Type 1) :
    F ⟶ (Over.pullback p ⋙ Over.map p).op ⋙ F where
  app T := F.map ((Over.mapPullbackAdj p).counit.app T.unop).op
  naturality {T U} f := by
    change F.map f ≫ F.map ((Over.mapPullbackAdj p).counit.app U.unop).op =
      F.map ((Over.mapPullbackAdj p).counit.app T.unop).op ≫
        F.map ((Over.pullback p ⋙ Over.map p).map f.unop).op
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg F.map (congrArg Quiver.Hom.op
      ((Over.mapPullbackAdj p).counit.naturality f.unop)).symm

theorem baseCoverRestrictionMap_app (F : (Over S)ᵒᵖ ⥤ Type 1) (T : Over S) :
    (baseCoverRestrictionMap p F).app (.op T) =
      F.map ((Over.mapPullbackAdj p).counit.app T).op := rfl

set_option backward.isDefEq.respectTransparency false in
theorem picard_baseCoverRestriction_injective [Flat p] [Surjective p] [QuasiCompact p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    (T : Over S) : Function.Injective ((baseCoverRestrictionMap p
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj).app (.op T)) := by
  let J := Scheme.fppfTopology.over S
  let F := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj
  let r := baseCoverRestrictionMap p F
  have : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme) := by
    change Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme))
    infer_instance
  have : Presheaf.IsLocallySurjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme) := by
    change Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme))
    infer_instance
  have hc : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme ≫ r) := by
    constructor
    intro V x y h
    obtain ⟨L, rfl⟩ := Quotient.exists_rep x
    obtain ⟨M, rfl⟩ := Quotient.exists_rep y
    let u := (Over.mapPullbackAdj p).counit.app V.unop
    have : Flat u.left := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst V.unop.hom p))
    have : Surjective u.left := inferInstanceAs (Surjective (CategoryTheory.Limits.pullback.fst V.unop.hom p))
    have : QuasiCompact u.left := inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.fst V.unop.hom p))
    have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app V (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app V (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
      apply Universal.PicardFaithfullyFlat.Construction.universal_relativePicard_eq_of_faithfullyFlat A hA u L M
      exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
        (h.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)))
    exact Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme) _ _ hrel
  have : Presheaf.IsLocallyInjective J r :=
    (Presheaf.comp_isLocallyInjective_iff J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme) r).mp hc
  apply (Presheaf.isLocallyInjective_iff_injective_of_separated J r ?_).mp this (.op T)
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).property).isSeparated

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousPicard_baseCoverRestriction_injective [Flat p] [Surjective p] [QuasiCompact p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    (T : Over S) : Function.Injective ((baseCoverRestrictionMap p
      A.homogeneousPicardSheaf.obj).app (.op T)) := by
  have : Mono A.homogeneousPicardSheafInclusion :=
    inferInstanceAs (Mono (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A.scheme))
  have hi : Function.Injective (A.homogeneousPicardSheafInclusion.hom.app (.op T)) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  intro x y h
  apply hi
  apply picard_baseCoverRestriction_injective p A hA T
  let u := (Over.mapPullbackAdj p).counit.app T
  exact (A.homogeneousPicardSheafInclusion.hom.naturality_apply u.op x).symm.trans
    ((congrArg (A.homogeneousPicardSheafInclusion.hom.app
      (.op ((Over.pullback p ⋙ Over.map p).obj T))) h).trans
        (A.homogeneousPicardSheafInclusion.hom.naturality_apply u.op y))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.BaseCoverInjection.Construction
