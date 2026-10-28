import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Spec Principal Image Ideal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecPrincipalImageIdeal.BundleCycles

noncomputable section

/-! A principal kernel of an actual affine ring map is the same
principal image ideal in scheme global sections. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)

theorem specMap_kernel_top :
    RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom =
      (RingHom.ker φ).comap (Scheme.ΓSpecIso (.of A)).hom.hom := by
  ext r
  change (Spec.map (CommRingCat.ofHom φ)).appTop r = 0 ↔ φ ((Scheme.ΓSpecIso (.of A)).hom r) = 0
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) r
  change (Scheme.ΓSpecIso (.of B)).hom ((Spec.map (CommRingCat.ofHom φ)).appTop r) =
    φ ((Scheme.ΓSpecIso (.of A)).hom r) at h
  constructor
  · intro hr
    exact h.symm.trans (by rw [hr, map_zero])
  · intro hr
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1
    rw [map_zero]
    exact h.trans hr

theorem specMap_principal_kernel (t : A) (hker : RingHom.ker φ = Ideal.span {t}) :
    RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom =
      Ideal.span {(Scheme.ΓSpecIso (.of A)).inv t} := by
  rw [specMap_kernel_top, hker]
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  exact (Ideal.map_symm e).symm.trans (by rw [Ideal.map_span, Set.image_singleton]; rfl)

theorem spec_regular_globalSection (t : A) (ht : IsRegular t) :
    IsRegular ((Scheme.ΓSpecIso (.of A)).inv t) :=
  RegularRingEquiv.BundleCycles.regular_ringEquiv (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm t ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecPrincipalImageIdeal.BundleCycles
