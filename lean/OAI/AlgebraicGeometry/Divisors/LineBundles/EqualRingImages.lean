import Mathlib.Algebra.Ring.Subring.Basic

/-! # Equal Ring Images -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EqualRingImages.BundleCycles

noncomputable section

/-! Equal embedded ring images give the actual compatible ring isomorphism. -/

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* T) (ψ : S →+* T) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (h : φ.range = ψ.range)

def equalRingImagesEquiv : R ≃+* S :=
  (RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun _ _ he => hφ (congrArg Subtype.val he), φ.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans
        (RingEquiv.ofBijective ψ.rangeRestrict
          ⟨fun _ _ he => hψ (congrArg Subtype.val he), ψ.rangeRestrict_surjective⟩).symm)

theorem equalRingImagesEquiv_apply (r : R) :
    ψ (equalRingImagesEquiv φ ψ hφ hψ h r) = φ r := by
  let e := RingEquiv.ofBijective ψ.rangeRestrict
    ⟨fun _ _ he => hψ (congrArg Subtype.val he), ψ.rangeRestrict_surjective⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((RingEquiv.subringCongr h) (φ.rangeRestrict r)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EqualRingImages.BundleCycles
