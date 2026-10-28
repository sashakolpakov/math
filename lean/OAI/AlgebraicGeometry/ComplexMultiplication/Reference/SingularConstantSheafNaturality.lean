import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantPullback
import OAI.AlgebraicTopology.Singular.SheafCochainRestriction

/-! # Singular Constant Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantSheafNaturality

noncomputable section

/-! # The original constant-to-singular inclusion commutes with pullback

Actual singular zero-chain augmentation is natural in the actual scheme-point
map. Sheafification therefore preserves the original constant inclusion square.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [CommRing R]

/-- Original singular cochain pullback fixes constant zero-cochains. -/
theorem originalSingularRestrictionRaw_constants (f : X ⟶ Y) :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ≫
        AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionToRawPushforward R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0 =
      ConstantPullback.originalConstantPresheafPullback f (AddCommGrpCat.of R) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) := by
  ext U r
  change R at r
  apply LinearMap.ext
  intro c
  change r * (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) (Opposite.op U)).hom
      (((AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenChainMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) U).f 0).hom c) =
    r * (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (Opposite.op ((Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj U))).hom c
  have h := AlgebraicTopology.Singular.SheafCochain.simplicialZeroAugmentation_naturality R
    (TopCat.toSSet.map (AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenToOpen (DeRhamPresheafPullback.originalAnalyticSchemeMap f) U))
  exact congrArg (r * ·) (congrArg (fun q ↦ q.hom c) h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheafification of the original constant-to-singular square under actual pullback. -/
theorem originalSingularRestrictionSheaf_constants (f : X ⟶ Y) :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ≫
        AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0 =
      ConstantPullback.originalConstantSheafPullback f (AddCommGrpCat.of R) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    _ _ ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
      (AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) 0)).property
  change toSheafify _ (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
        (AddCommGrpCat.of R)) ≫
      sheafifyMap _ (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≫
        (AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0).hom =
    toSheafify _ (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
        (AddCommGrpCat.of R)) ≫
      ConstantPullback.originalConstantSheafPullbackHom f (AddCommGrpCat.of R) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (sheafifyMap _ (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    AlgebraicTopology.Singular.SheafCochainRestriction.toSheafify_comp_singularRestrictionSheaf]
  change AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ≫
      AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionToRawPushforward R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0 ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (toSheafify _ (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) 0)) = _
  rw [← Category.assoc, originalSingularRestrictionRaw_constants, Category.assoc,
    ← Functor.map_comp, toSheafify_naturality, Functor.map_comp,
    ← Category.assoc, ← ConstantPullback.originalConstantSheafPullback_unit]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantSheafNaturality
