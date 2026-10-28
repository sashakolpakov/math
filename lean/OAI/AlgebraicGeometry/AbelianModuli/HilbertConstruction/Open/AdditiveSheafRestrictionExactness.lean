import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionLimits

/-! # Additive Sheaf Restriction Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionExactness.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

noncomputable instance openSheafPullback_preservesFiniteColimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteColimits (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U) := by
  change PreservesFiniteColimits
    (U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})
  let : PreservesColimits
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.ι.base) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction
      AddCommGrpCat.{u} U.ι.base).leftAdjoint_preservesColimits
  exact preservesFiniteColimits_of_natIso
    (U.ι.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionExactness.ZariskiCohomology.LocalKilling
