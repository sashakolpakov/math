import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel

/-! # Product Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductRestriction.Construction

noncomputable section

/-! Products of actual ideal sheaves under affine identification and open pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_comap_mul_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Bijective g) (I J : Ideal S) :
    (I * J).comap g = I.comap g * J.comap g := by
  let e := RingEquiv.ofBijective g hg
  change (I * J).comap e = I.comap e * J.comap e
  rw [← Ideal.map_symm e, Ideal.map_mul, Ideal.map_symm e, Ideal.map_symm e]

universe u

/-- Affine quotient kernel sheaves preserve the actual ideal product. -/
theorem affineQuotientKernel_mul {R : Type u} [CommRing R] (I J : Ideal R) :
    Affine.QuotientKernel.Construction.affineQuotientKernel (I * J) = Affine.QuotientKernel.Construction.affineQuotientKernel I * Affine.QuotientKernel.Construction.affineQuotientKernel J := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  change (I * J).comap (Scheme.ΓSpecIso (.of R)).hom.hom =
    (Affine.QuotientKernel.Construction.affineQuotientKernel I).ideal ⟨⊤, isAffineOpen_top _⟩ *
      (Affine.QuotientKernel.Construction.affineQuotientKernel J).ideal ⟨⊤, isAffineOpen_top _⟩
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact ideal_comap_mul_of_bijective _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.bijective I J

/-- Native products commute with actual open pullback. -/
theorem idealSheaf_comap_mul_open {X Y : Scheme.{u}} (I J : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] :
    (I * J).comap g = I.comap g * J.comap g := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change ((I.ideal ⟨g ''ᵁ U, U.2.image_of_isOpenImmersion g⟩) *
    (J.ideal ⟨g ''ᵁ U, U.2.image_of_isOpenImmersion g⟩)).comap (g.appIso U).inv.hom =
      (I.comap g).ideal U * (J.comap g).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact ideal_comap_mul_of_bijective (g.appIso U).inv.hom
    (g.appIso U).symm.commRingCatIsoToRingEquiv.bijective _ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductRestriction.Construction
