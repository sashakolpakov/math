import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.RestrictionSpan
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr

/-! # Projective Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveDiagram.BundleCycles

noncomputable section

/-! The actual projective augmented conormal spectra and their
restriction maps form a functor on the affine Zariski site. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev conormalProjectiveChart (U : X.AffineZariskiSite) : Scheme :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme (Γ(X, U.1) ⧸ I.ideal U)
    ((Γ(X, U.1) ⧸ I.ideal U) × (I.ideal U).Cotangent)

def conormalProjectiveGradedMap {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction (I.ideal V) (I.ideal U)
    (X.presheaf.map ((toOpensFunctor X).map i).op).hom
    (I.ideal_le_comap_ideal (toOpens_mono i.le))

theorem conormalProjectiveGradedMap_irrelevant {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (Γ(X, U.1) ⧸ I.ideal U)
      ((Γ(X, U.1) ⧸ I.ideal U) × (I.ideal U).Cotangent)) ≤
    (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (Γ(X, V.1) ⧸ I.ideal V)
      ((Γ(X, V.1) ⧸ I.ideal V) × (I.ideal V).Cotangent))).map (conormalProjectiveGradedMap I i) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap_span _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i))

def conormalProjectiveRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    conormalProjectiveChart I U ⟶ conormalProjectiveChart I V :=
  Proj.map (conormalProjectiveGradedMap I i) (conormalProjectiveGradedMap_irrelevant I i)

theorem conormalProjectiveGradedMap_id (U : X.AffineZariskiSite) :
    conormalProjectiveGradedMap I (𝟙 U) = GradedRingHom.id _ := by
  have h : (X.presheaf.map ((toOpensFunctor X).map (𝟙 U)).op).hom = RingHom.id Γ(X, U.1) :=
    congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id (.op U))
  exact (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction_congr _ _ h _ _).trans
    (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction_id _)

theorem conormalProjectiveGradedMap_comp {U V W : X.AffineZariskiSite} (f : U ⟶ V) (g : V ⟶ W) :
    conormalProjectiveGradedMap I (f ≫ g) =
      (conormalProjectiveGradedMap I f).comp (conormalProjectiveGradedMap I g) := by
  have h : (X.presheaf.map ((toOpensFunctor X).map (f ≫ g)).op).hom =
      ((X.presheaf.map ((toOpensFunctor X).map f).op).hom).comp
        (X.presheaf.map ((toOpensFunctor X).map g).op).hom :=
    congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp g.op f.op)
  exact (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction_congr _ _ h _ _).trans
    (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction_comp _ _ _ _ _ _ _).symm

def conormalProjectiveDiagram : X.AffineZariskiSite ⥤ Scheme where
  obj U := conormalProjectiveChart I U
  map i := conormalProjectiveRestriction I i
  map_id U :=
    (Projective.MapCongr.BundleCycles.projectiveMap_congr (conormalProjectiveGradedMap_id I U) _ (by simp)).trans Proj.map_id
  map_comp f g :=
    (Projective.MapCongr.BundleCycles.projectiveMap_congr (conormalProjectiveGradedMap_comp I f g) _
      (HomogeneousIdeal.irrelevant_le_map_comp (conormalProjectiveGradedMap_irrelevant I g)
        (conormalProjectiveGradedMap_irrelevant I f))).trans
      (Proj.map_comp (conormalProjectiveGradedMap I g) (conormalProjectiveGradedMap I f)
        (conormalProjectiveGradedMap_irrelevant I g) (conormalProjectiveGradedMap_irrelevant I f))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveDiagram.BundleCycles
