import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ColonRestriction

/-! # Quotient Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel.Construction

noncomputable section

/-! The kernel ideal sheaf of an affine quotient, with its exact ideal operations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

abbrev affineQuotientKernel (I : Ideal R) : (Spec (.of R)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

/-- Global sections identify the actual affine quotient kernel with the
original ring ideal, via the canonical spectrum-sections isomorphism. -/
theorem affineQuotientKernel_idealTop (I : Ideal R) :
    (affineQuotientKernel I).ideal ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ =
      I.comap (Scheme.ΓSpecIso (.of R)).hom.hom := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ).appTop.hom = _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of (R ⧸ I))).commRingCatIsoToRingEquiv]
  change RingHom.ker ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
    (Scheme.ΓSpecIso (.of (R ⧸ I))).hom).hom = _
  rw [Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
  change (RingHom.ker (Ideal.Quotient.mk I)).comap (Scheme.ΓSpecIso (.of R)).hom.hom = _
  rw [Ideal.mk_ker]

/-- Taking the power of a ring ideal gives the power of its actual kernel ideal sheaf. -/
theorem affineQuotientKernel_pow (I : Ideal R) (n : ℕ) :
    affineQuotientKernel (I ^ n) = (affineQuotientKernel I) ^ n := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [affineQuotientKernel_idealTop]
  change (I ^ n).comap (Scheme.ΓSpecIso (.of R)).hom.hom =
    ((affineQuotientKernel I).ideal ⟨⊤, isAffineOpen_top (Spec (.of R))⟩) ^ n
  rw [affineQuotientKernel_idealTop]
  exact IdealSheaf.ColonRestriction.Construction.ideal_comap_pow_of_bijective (Scheme.ΓSpecIso (.of R)).hom.hom
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.bijective I n

variable [IsNoetherianRing R]

/-- The native quotient of affine kernel ideal sheaves is exactly the
kernel ideal sheaf of the original algebraic colon ideal. -/
theorem affineQuotientKernel_colon (J K : Ideal R) :
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (affineQuotientKernel J) (affineQuotientKernel K) =
      affineQuotientKernel (J.colon (K : Set R)) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal, affineQuotientKernel_idealTop,
    affineQuotientKernel_idealTop, affineQuotientKernel_idealTop]
  exact (IdealSheaf.ColonRestriction.Construction.ideal_comap_colon_of_surjective (Scheme.ΓSpecIso (.of R)).hom.hom
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.surjective J K).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel.Construction
