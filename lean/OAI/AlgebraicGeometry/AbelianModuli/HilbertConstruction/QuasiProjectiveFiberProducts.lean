import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Quasi Projective Fiber Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveFiberProducts

noncomputable section

/-! Fiber products of actual quasi-projective presentations over a
separated parameter remain quasi-projective. The construction is the
closed equalizer inside the product of the given compactifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u v

private def cartesianPullbackEqualizerIso
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [HasPullbacks C] [HasEqualizers C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ equalizer (fst X Y ≫ f) (snd X Y ≫ g) where
  hom := equalizer.lift (lift (pullback.fst f g) (pullback.snd f g)) (by
    simpa only [lift_fst_assoc, lift_snd_assoc] using (pullback.condition (f := f) (g := g)))
  inv := pullback.lift
    (equalizer.ι (fst X Y ≫ f) (snd X Y ≫ g) ≫ fst X Y)
    (equalizer.ι (fst X Y ≫ f) (snd X Y ≫ g) ≫ snd X Y) (by
      simpa only [Category.assoc] using (equalizer.condition (fst X Y ≫ f) (snd X Y ≫ g)))
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [Category.assoc, pullback.lift_fst, pullback.lift_snd]
  inv_hom_id := by
    apply (cancel_mono (equalizer.ι (fst X Y ≫ f) (snd X Y ≫ g))).mp
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [Category.assoc, pullback.lift_fst, pullback.lift_snd]

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation.fiberProduct
    {S : Scheme.{u}} [IsNoetherian S] {X Y Z : Over S}
    (P : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsSeparated Z.hom] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (pullback f g) := by
  let e := cartesianPullbackEqualizerIso f g
  letI : IsClosedImmersion e.hom.left := Grassmann.ProjectivePresentation.overIso_closedImmersion e
  exact ((P.product Q).ofClosedImmersion
    (equalizer.ι (fst X Y ≫ f) (snd X Y ≫ g))).ofClosedImmersion e.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveFiberProducts
