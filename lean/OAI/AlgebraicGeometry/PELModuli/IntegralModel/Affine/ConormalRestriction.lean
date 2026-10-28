import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalEtale
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Conormal Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ConormalRestriction.AffineSectionConormal

noncomputable section

section

/-! Conormal maps and their restriction isomorphisms are induced by
the actual maps between affine smooth section neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection.BundleCycles

variable {X Y Z : Scheme.{0}}

def sectionAlgebraHom (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    Γ(Y, ⊤) →ₐ[Γ(X, ⊤)] Γ(X, ⊤) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  exact { s.appTop.hom with
    commutes' := fun r => ConcreteCategory.congr_hom (Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.section_appTop p s hs) r }

def ambientAlgebraHom (p : Y ⟶ X) (q : Z ⟶ X) (f : Y ⟶ Z) (hf : f ≫ q = p) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
    Γ(Z, ⊤) →ₐ[Γ(X, ⊤)] Γ(Y, ⊤) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
  refine { f.appTop.hom with commutes' := ?_ }
  intro r
  exact ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop f q).symm.trans (congrArg Scheme.Hom.appTop hf)) r

theorem section_comp (p : Y ⟶ X) (q : Z ⟶ X)
    (s : X ⟶ Y) (t : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (ht : t ≫ q = 𝟙 X)
    (f : Y ⟶ Z) (hf : f ≫ q = p) (he : s ≫ f = t) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
    (sectionAlgebraHom p s hs).comp (ambientAlgebraHom p q f hf) = sectionAlgebraHom q t ht := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
  apply AlgHom.ext
  intro r
  exact ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop s f).symm.trans (congrArg Scheme.Hom.appTop he)) r

def map (p : Y ⟶ X) (q : Z ⟶ X)
    (s : X ⟶ Y) (t : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (ht : t ≫ q = 𝟙 X)
    (f : Y ⟶ Z) (hf : f ≫ q = p) (he : s ≫ f = t) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
    (RingHom.ker t.appTop.hom).Cotangent →ₗ[Γ(X, ⊤)] (RingHom.ker s.appTop.hom).Cotangent := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
  exact Section.ConormalMaps.SectionConormal.map (sectionAlgebraHom q t ht) (sectionAlgebraHom p s hs)
    (ambientAlgebraHom p q f hf) (section_comp p q s t hs ht f hf he)

theorem finite_projective [IsAffine X] [IsAffine Y]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    Module.Finite Γ(X, ⊤) (RingHom.ker s.appTop.hom).Cotangent ∧
      Module.Projective Γ(X, ⊤) (RingHom.ker s.appTop.hom).Cotangent := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  exact Section.ConormalMaps.SectionConormal.finite_projective (sectionAlgebraHom p s hs)

end

/-! The conormal map of an actual étale map between smooth affine
section neighborhoods is bijective. This identifies conormals on smaller charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SchemeSection.BundleCycles

theorem map_bijective_of_etale {X Y Z : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (p : Y ⟶ X) (q : Z ⟶ X) [Smooth p] [Smooth q]
    (s : X ⟶ Y) (t : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (ht : t ≫ q = 𝟙 X)
    (f : Y ⟶ Z) [Etale f] (hf : f ≫ q = p) (he : s ≫ f = t) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
    Function.Bijective (map p q s t hs ht f hf he) := by
  let R := Γ(X, ⊤)
  let B := Γ(Z, ⊤)
  let C := Γ(Y, ⊤)
  let : Algebra R B := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
  let : Algebra R C := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let : Algebra B C := f.appTop.hom.toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r =>
    (ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop f q).symm.trans
      (congrArg Scheme.Hom.appTop hf)) r).symm
  let : Algebra B R := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra t
  let : Algebra C R := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let : IsScalarTower R B R := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower q t ht
  let : IsScalarTower R C R := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let : IsScalarTower B C R := IsScalarTower.of_algebraMap_eq fun b =>
    (ConcreteCategory.congr_hom ((Scheme.Hom.comp_appTop s f).symm.trans
      (congrArg Scheme.Hom.appTop he)) b).symm
  let : Algebra.Smooth R B := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth q
  let : Algebra.Smooth R C := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  let : Algebra.Etale B C := HasRingHomProperty.appTop (P := @Etale) f inferInstance
  have hmap : (Section.ConormalEtale.SectionConormal.etaleEquiv R B C).toLinearMap = map p q s t hs ht f hf he := by
    apply LinearMap.ext
    intro v
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker t.appTop.hom) v
    exact Section.ConormalEtale.SectionConormal.etaleEquiv_toCotangent R B C b
  rw [← hmap]
  exact (Section.ConormalEtale.SectionConormal.etaleEquiv R B C).bijective

def restrictionEquiv {X Y Z : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (p : Y ⟶ X) (q : Z ⟶ X) [Smooth p] [Smooth q]
    (s : X ⟶ Y) (t : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (ht : t ≫ q = 𝟙 X)
    (f : Y ⟶ Z) [Etale f] (hf : f ≫ q = p) (he : s ≫ f = t) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
    (RingHom.ker t.appTop.hom).Cotangent ≃ₗ[Γ(X, ⊤)] (RingHom.ker s.appTop.hom).Cotangent := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra q
  exact LinearEquiv.ofBijective (map p q s t hs ht f hf he)
    (map_bijective_of_etale p q s t hs ht f hf he)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ConormalRestriction.AffineSectionConormal
