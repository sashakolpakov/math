import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProjectedCechComplexPullback

/-! # Morphism Ordinary Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback

noncomputable section

/-! The original ordinary algebraic comparison on affine pairs
uses exactly geometric de Rham pullback to the actual smaller opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def openMap : MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f ⟶
    MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f ⋙ RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f.left where
  app U := homOfLE U.property
  naturality _ _ _ := Subsingleton.elim _ _

theorem coordinates : MorphismOrdinaryForms.AffineMorphismOrdinaryForms.map R f =
    ProjectedCechComplexPullback.SmallProjectedCechComplexPullback.pairedMap R f.left
      (MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f) (MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f)
      (openMap R f) (DeRhamPullbackTo.DeRhamPullback.presheafPullback f) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  exact MorphismOrdinaryForms.AffineMorphismOrdinaryForms.original_pullback R f q U

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback
