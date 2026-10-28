import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionRing

/-! # Chart Section Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionAlgebra

noncomputable section

/-!
# IntegralComparison: affine chart section coordinates retain the native base-algebra action
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C : Type u) [CommRing k] [CommRing C] [Algebra k C]
  (X : Over (Spec (CommRingCat.of k))) (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g]
  (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k C)))

def equiv : ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op g.opensRange)) ≃ₐ[k] C where
  toRingEquiv := (ChartSectionRing.iso k C X g).commRingCatIsoToRingEquiv
  commutes' r := by
    have h := ConcreteCategory.congr_hom (ChartSectionRing.base_square k C X g hg) r
    have he := ConcreteCategory.congr_hom (ChartSectionRing.iso_hom k C X g)
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X g.opensRange r)
    exact he.trans h

def iso : (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op g.opensRange) ≅ CommAlgCat.of k C :=
  CommAlgCat.isoMk (equiv k C X g hg)

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op g.opensRange)) ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C :=
  (OrdinaryDeRhamFunctor.Ordinary.functor k).mapIso (iso k C X g hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionAlgebra
