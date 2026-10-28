import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Algebra

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Kernel

noncomputable section

/-! The original closed-immersion algebraic stalk kernel is the localization of its actual affine section kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closedImmersion_stalkMap_ker
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (hU : IsAffineOpen U) (x : X) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      Ideal.map (Y.presheaf.germ U (f x) hx).hom (RingHom.ker (f.app U).hom) := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let pA := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let pB := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (f x)) := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) pA := hU.isLocalization_stalk ⟨f x, hx⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) pB := hV.isLocalization_stalk ⟨x, hx⟩
  have hp : Ideal.comap (f.app U).hom pB = pA := by
    have h := congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hx)
    change Ideal.comap (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom pB = pA at h
    rw [← f.app_eq_appLE] at h
    exact h
  have hS : Submonoid.map (f.app U).hom pA.primeCompl = pB.primeCompl := by
    have hpc : (pB.comap (f.app U).hom).primeCompl = pA.primeCompl := by
      ext a
      change a ∉ pB.comap (f.app U).hom ↔ a ∉ pA
      rw [hp]
    exact (congrArg (Submonoid.map (f.app U).hom) hpc).symm.trans
      (Ideal.map_primeCompl_comap_of_surjective (f.app U).hom (f.app_surjective U hU) pB)
  have hmap : (f.stalkMap x).hom =
      (IsLocalization.map (X.presheaf.stalk x) (f.app U).hom
        (hS.symm ▸ pA.primeCompl.le_comap_map) : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x) := by
    apply IsLocalization.ringHom_ext pA.primeCompl
    apply RingHom.ext
    intro a
    change (f.stalkMap x) (Y.presheaf.germ U (f x) hx a) =
      IsLocalization.map (X.presheaf.stalk x) (f.app U).hom
        (hS.symm ▸ pA.primeCompl.le_comap_map) (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x)) a)
    rw [IsLocalization.map_eq]
    exact f.germ_stalkMap_apply U x hx a
  rw [hmap]
  exact IsLocalization.ker_map (S := Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (f.app U).hom hS

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Kernel
