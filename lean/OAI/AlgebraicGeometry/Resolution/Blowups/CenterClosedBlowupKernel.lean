import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupClosedKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupComplement
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ClosedImageRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities

/-! # Center Closed Blowup Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CenterClosedBlowupKernel.Construction

noncomputable section

/-! Away from the center, the closed blowup kernel is the unchanged total ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMap_unitCenter_ker {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (I H : Ideal R) (hI : I = ⊤)
    (φ : R →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ = H) (b : ℕ) :
    (ReesMap.Construction.affineBlowupMap I φ).ker = Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf I H b := by
  subst I
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup (⊤ : Ideal R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R))
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R)) := Affine.BlowupComplement.Construction.affineBlowupToSpec_unitIdeal_isIso
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec ((⊤ : Ideal R).map φ)) := by
    rw [Ideal.map_top]
    exact Affine.BlowupComplement.Construction.affineBlowupToSpec_unitIdeal_isIso
  let : IsClosedImmersion (ReesMap.Construction.affineBlowupMap (⊤ : Ideal R) φ) :=
    Blowup.ClosedMap.Construction.affineBlowupMap_isClosedImmersion _ φ hφ
  rw [← Locally.ClosedImageRestriction.Construction.kernel_comap_of_comp_open (ReesMap.Construction.affineBlowupMap (⊤ : Ideal R) φ)
    (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R)), Blowup.BaseOpen.Construction.affineBlowupMap_over,
    Scheme.Hom.ker_comp_of_isIso, Affine.BlowupKernelSheaf.Construction.specMap_kernel_eq_affineQuotientKernel, hker]
  unfold Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top, Scheme.IdealSheafData.comap_top,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, Scheme.IdealSheafData.one_eq_top,
    GlobalControlled.Identities.Construction.noetherianIdealSheafColon_top_right]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CenterClosedBlowupKernel.Construction
