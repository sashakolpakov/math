import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductRestriction

/-! # Kernel Sums -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums.Construction

noncomputable section

/-! Arbitrary sums under the actual affine quotient-kernel identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_comap_iSup_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Bijective g) {ι : Type*} (I : ι → Ideal S) :
    (⨆ i, I i).comap g = ⨆ i, (I i).comap g := by
  let e := RingEquiv.ofBijective g hg
  change (⨆ i, I i).comap e = ⨆ i, (I i).comap e
  rw [← Ideal.map_symm e, Ideal.map_iSup]
  simp only [Ideal.map_symm e]

theorem affineQuotientKernel_iSup {R : Type*} [CommRing R] {ι : Type*} (I : ι → Ideal R) :
    QuotientKernel.Construction.affineQuotientKernel (⨆ i, I i) = ⨆ i, QuotientKernel.Construction.affineQuotientKernel (I i) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [QuotientKernel.Construction.affineQuotientKernel_idealTop, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  simp only [QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact ideal_comap_iSup_of_bijective _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.bijective I

theorem idealSheaf_comap_iSup {X Y : Scheme} {ι : Type*} (I : ι → Y.IdealSheafData)
    (g : X ⟶ Y) : (⨆ i, I i).comap g = ⨆ i, (I i).comap g :=
  (Scheme.IdealSheafData.map_gc g).l_iSup

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums.Construction
