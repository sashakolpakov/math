import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel

/-! # Kernel Zero -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelZero.Construction

noncomputable section

/-! The zero ring ideal defines the zero native affine ideal sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineQuotientKernel_bot {R : Type*} [CommRing R] :
    QuotientKernel.Construction.affineQuotientKernel (⊥ : Ideal R) = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [QuotientKernel.Construction.affineQuotientKernel_idealTop]
  change (⊥ : Ideal R).comap (Scheme.ΓSpecIso (.of R)).hom.hom = ⊥
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelZero.Construction
