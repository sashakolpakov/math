import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform

/-! # Whole Prefix Companion Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An arbitrary uniform-incidence companion prefix transports both the residual ideal and its boundary-monomial product through the same blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_companion_same_blowups
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m * (b - m)) X f C Y g K) :
    ∀ [Smooth f] (β : Type) [Fintype β] (D : β → X.IdealSheafData), P.uniformBoundaryCompatible β D →
      ∀ (J : X.IdealSheafData) (a : β → ℕ), C = Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b →
      ∃ (J' : Y.IdealSheafData) (a' : P.endpointLabels β → ℕ)
        (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g J')
        (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) Y g
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.endpointBoundary D) a' * J')),
        Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) m P R ∧ Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) b P Q ∧
          K = Global.CompanionIdeal.Construction.globalCompanionIdeal J' (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.endpointBoundary D) a') m b := by
  induction P with
  | stop =>
      intro _ β _ D hD J a hC
      exact ⟨J, a, .stop, .stop, .stop, .stop, hC⟩
  | @blowup X hX hNX f C I hI hc hp hs hbl Y g K tail ih =>
      intro hf β _ D hD J a hC
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      obtain ⟨A, F, hF⟩ := hD.1
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
      let a₁ := Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) F
      let J₁ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m
      obtain ⟨hJ, hM, hpTotal⟩ := Global.CompanionIdeal.Construction.globalCompanionIdeal_smooth_center_permissible
        f I J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b hm hmb (hC ▸ hp)
      have hmon : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI (b - m) =
          Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ :=
        A.monomial_transform_uniform_incidence F (fun i _ => hF i) hI a (b - m) hM
      have hcomp : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I C hI (m * (b - m)) =
          Global.CompanionIdeal.Construction.globalCompanionIdeal J₁ (Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁) m b := by
        rw [hC, Global.CompanionTransform.Construction.globalBlowup_companion_transform I J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI m b hJ hM, hmon]
      have hproduct : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
          Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ * J₁ := by
        rw [Global.CompanionTransform.Construction.globalBlowup_companion_product_transform I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) J hI m b (Nat.le_of_lt hmb) hM hJ, hmon]
      obtain ⟨J', a', R, Q, hR, hQ, hK⟩ := ih (Option β) D' hD.2 J₁ a₁ hcomp
      have hnext : ∃ S : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b) Y g
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (tail.endpointBoundary D') a' * J'),
          Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) b tail S := by
        rw [hproduct]
        exact ⟨Q, hQ⟩
      obtain ⟨S, hS⟩ := hnext
      have hb : 0 < b := hm.trans hmb
      exact ⟨J', a', .blowup I hI hm hJ hs hbl R, .blowup I hI hb hpTotal hs hbl S,
        .blowup I hI hc hm hp hJ hs hbl hR, .blowup I hI hc hb hp hpTotal hs hbl hS, hK⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
