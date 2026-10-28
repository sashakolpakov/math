import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.RestrictionSpan
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.GradedRestriction

/-! # Infinity Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityDiagram.BundleCycles

noncomputable section

/-! The actual projective conormal spectra and their
restriction maps form a functor on the affine Zariski site. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev conormalInfinityChart (U : X.AffineZariskiSite) : Scheme :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme (Γ(X, U.1) ⧸ I.ideal U)
    (I.ideal U).Cotangent

def conormalInfinityGradedMap {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  GradedRestriction.BundleCycles.conormalGradedRestriction (I.ideal V) (I.ideal U)
    (X.presheaf.map ((toOpensFunctor X).map i).op).hom
    (I.ideal_le_comap_ideal (toOpens_mono i.le))

theorem conormalInfinityGradedMap_irrelevant {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (Γ(X, U.1) ⧸ I.ideal U)
      (I.ideal U).Cotangent) ≤
    (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (Γ(X, V.1) ⧸ I.ideal V)
      (I.ideal V).Cotangent)).map (conormalInfinityGradedMap I i) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i)

def conormalInfinityRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    conormalInfinityChart I U ⟶ conormalInfinityChart I V :=
  Proj.map (conormalInfinityGradedMap I i) (conormalInfinityGradedMap_irrelevant I i)

theorem conormalInfinityGradedMap_id (U : X.AffineZariskiSite) :
    conormalInfinityGradedMap I (𝟙 U) = GradedRingHom.id _ := by
  have h : (X.presheaf.map ((toOpensFunctor X).map (𝟙 U)).op).hom = RingHom.id Γ(X, U.1) :=
    congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id (.op U))
  exact (GradedRestriction.BundleCycles.conormalGradedRestriction_congr _ _ h _ _).trans
    (GradedRestriction.BundleCycles.conormalGradedRestriction_id _)

theorem conormalInfinityGradedMap_comp {U V W : X.AffineZariskiSite} (f : U ⟶ V) (g : V ⟶ W) :
    conormalInfinityGradedMap I (f ≫ g) =
      (conormalInfinityGradedMap I f).comp (conormalInfinityGradedMap I g) := by
  have h : (X.presheaf.map ((toOpensFunctor X).map (f ≫ g)).op).hom =
      ((X.presheaf.map ((toOpensFunctor X).map f).op).hom).comp
        (X.presheaf.map ((toOpensFunctor X).map g).op).hom :=
    congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp g.op f.op)
  exact (GradedRestriction.BundleCycles.conormalGradedRestriction_congr _ _ h _ _).trans
    (GradedRestriction.BundleCycles.conormalGradedRestriction_comp _ _ _ _ _ _ _).symm

def conormalInfinityDiagram : X.AffineZariskiSite ⥤ Scheme where
  obj U := conormalInfinityChart I U
  map i := conormalInfinityRestriction I i
  map_id U :=
    (Projective.MapCongr.BundleCycles.projectiveMap_congr (conormalInfinityGradedMap_id I U) _ (by simp)).trans Proj.map_id
  map_comp f g :=
    (Projective.MapCongr.BundleCycles.projectiveMap_congr (conormalInfinityGradedMap_comp I f g) _
      (HomogeneousIdeal.irrelevant_le_map_comp (conormalInfinityGradedMap_irrelevant I g)
        (conormalInfinityGradedMap_irrelevant I f))).trans
      (Proj.map_comp (conormalInfinityGradedMap I g) (conormalInfinityGradedMap I f)
        (conormalInfinityGradedMap_irrelevant I g) (conormalInfinityGradedMap_irrelevant I f))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityDiagram.BundleCycles
