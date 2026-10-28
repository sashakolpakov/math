import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupComplement
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedAffineCenterExtension

/-! # Supported Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SupportedCenterBlowup.Construction

noncomputable section

/-! The actual blowup of an extended affine center agrees with the local
blowup and with the identity away from that center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- The blowup of the contracted ideal restricts to exactly the original
local blowup. No support or nonzero-ideal hypothesis is needed for this square. -/
theorem affineBlowup_contracted_center_isPullback
    (f : R) (C : Ideal (Localization.Away f)) :
    let I := C.comap (algebraMap R (Localization.Away f))
    ∃ j : ReesGrading.Construction.affineBlowup C ⟶ ReesGrading.Construction.affineBlowup I,
      IsPullback j (ReesGrading.Construction.affineBlowupToSpec C) (ReesGrading.Construction.affineBlowupToSpec I)
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  let I := C.comap (algebraMap R (Localization.Away f))
  have hex : ∃ j : ReesGrading.Construction.affineBlowup (I.map (algebraMap R (Localization.Away f))) ⟶ ReesGrading.Construction.affineBlowup I,
      IsPullback j (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R (Localization.Away f))))
        (ReesGrading.Construction.affineBlowupToSpec I)
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
    ⟨ReesMap.Construction.affineBlowupMap I (algebraMap R (Localization.Away f)), Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback I⟩
  have hmap : I.map (algebraMap R (Localization.Away f)) = C :=
    IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) C
  rw [hmap] at hex
  exact hex

/-- The original principal open and the center complement cover the
whole affine scheme when the center is supported inside the open. -/
theorem supported_center_target_open_cover
    (I : Ideal R) (f : R)
    (hpoints : ∀ q : Ideal R, q ≠ ⊤ → I ≤ q → f ∉ q) :
    PrimeSpectrum.basicOpen f ⊔ Affine.BlowupComplement.Construction.affineCenterComplement I = ⊤ := by
  apply top_unique
  intro q _
  by_cases hfq : f ∈ q.asIdeal
  · right
    change ¬ I ≤ q.asIdeal
    intro hIq
    exact hpoints q.asIdeal (inferInstance : q.asIdeal.IsPrime).ne_top hIq hfq
  · left
    exact hfq

/-- The extended center yields an actual proper global affine step.
Its local blowup and identity-complement descriptions cover the base. -/
theorem supported_affine_center_blowup_step [IsNoetherianRing R]
    (F : Ideal R) (f : R) (hf : 1 - f ∈ F)
    (C : Ideal (Localization.Away f)) (N : ℕ)
    (hC : (F ^ N).map (algebraMap R (Localization.Away f)) ≤ C) :
    let I := C.comap (algebraMap R (Localization.Away f))
    IsProper (ReesGrading.Construction.affineBlowupToSpec I) ∧
      (∃ j : ReesGrading.Construction.affineBlowup C ⟶ ReesGrading.Construction.affineBlowup I,
        IsPullback j (ReesGrading.Construction.affineBlowupToSpec C) (ReesGrading.Construction.affineBlowupToSpec I)
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))) ∧
      IsIso (ReesGrading.Construction.affineBlowupToSpec I ∣_ Affine.BlowupComplement.Construction.affineCenterComplement I) ∧
      PrimeSpectrum.basicOpen f ⊔ Affine.BlowupComplement.Construction.affineCenterComplement I = ⊤ := by
  let I := C.comap (algebraMap R (Localization.Away f))
  have hext := SupportedAffineCenterExtension.Construction.supported_affine_center_extension F f hf C N hC
  exact ⟨inferInstance, affineBlowup_contracted_center_isPullback f C,
    Affine.BlowupComplement.Construction.affineBlowup_centerComplement_isIso I, supported_center_target_open_cover I f hext.2.2⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SupportedCenterBlowup.Construction
