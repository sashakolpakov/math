import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport

/-! # Coefficient Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the affine coefficient rings of a closed support

The coefficients are the actual quotients by the support ideal sheaf.
Their transition maps and the images of the center ideals are compatible
with restrictions, with no cohomological condition in the construction.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Taking the image of a center ideal commutes with the coefficient quotient map. -/
theorem ideal_image_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (I P : Ideal R) (J Q : Ideal S) (f : R →+* S)
    (hP : P ≤ Q.comap f) (hI : I.map f = J) :
    (I.map (Ideal.Quotient.mk P)).map (Ideal.quotientMap Q f hP) =
      J.map (Ideal.Quotient.mk Q) := by
  rw [Ideal.map_map, Ideal.quotientMap_comp_mk, ← Ideal.map_map, hI]

variable {X : Scheme.{u}} (P : X.IdealSheafData)

/-- The coefficient rings of the closed support on all affine opens of the ambient scheme. -/
def supportCoefficientDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Γ(X, U.unop.1) ⧸ P.ideal U.unop)
  map {U V} f := CommRingCat.ofHom
    (Ideal.quotientMap (P.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (P.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (P.ideal U.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map (𝟙 U) r) =
      Ideal.Quotient.mk (P.ideal U.unop) r
    exact congrArg (Ideal.Quotient.mk (P.ideal U.unop))
      (ConcreteCategory.congr_hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id U) r)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (P.ideal W.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map (f ≫ g) r) =
      Ideal.Quotient.mk (P.ideal W.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map g
          (((toOpensFunctor X).op ⋙ X.presheaf).map f r))
    exact congrArg (Ideal.Quotient.mk (P.ideal W.unop))
      (ConcreteCategory.congr_hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp f g) r)

/-- The actual quotient maps form the coefficient natural transformation. -/
def supportCoefficientMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ supportCoefficientDiagram P where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U.unop))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl

/-- The actual quotient coefficient rings commute with affine basic-open localization. -/
theorem supportCoefficientMap_coequifibered : (supportCoefficientMap P).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hP : (P.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = P.ideal V :=
    P.map_ideal_basicOpen U r
  have h := QuotientLocalization.BundleCycles.quotientMap_isLocalization (Submonoid.powers r) Γ(X, V.1)
    (P.ideal U) (P.ideal V) hP (P.ideal_le_comap_ideal (X.basicOpen_le r))
  simp only [Submonoid.map_powers] at h
  exact h

variable (I : X.IdealSheafData)

/-- The restricted center ideal in each actual support coefficient ring. -/
def supportCenterIdeal (U : X.AffineZariskiSite) :
    Ideal ((supportCoefficientDiagram P).obj (.op U)) :=
  (I.ideal U).map (Ideal.Quotient.mk (P.ideal U))

theorem supportCenterIdeal_map {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (supportCenterIdeal P I U.unop).map ((supportCoefficientDiagram P).map f).hom =
      supportCenterIdeal P I V.unop :=
  ideal_image_quotientMap (I.ideal U.unop) (P.ideal U.unop)
    (I.ideal V.unop) (P.ideal V.unop)
    (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
    (P.ideal_le_comap_ideal (toOpens_mono f.unop.le))
    (I.map_ideal (toOpens_mono f.unop.le))

theorem supportCenterIdeal_le_comap {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    supportCenterIdeal P I U.unop ≤
      (supportCenterIdeal P I V.unop).comap ((supportCoefficientDiagram P).map f).hom :=
  Ideal.map_le_iff_le_comap.mp (supportCenterIdeal_map P I f).le

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram.BundleCycles
