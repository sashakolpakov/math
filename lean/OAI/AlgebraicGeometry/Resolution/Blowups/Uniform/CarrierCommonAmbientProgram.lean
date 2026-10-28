import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierPullbackStep
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierPrefixEtale

/-! # Carrier Common Ambient Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

section

/-! A common coefficient program constructs one actual ambient carrier lift comparing both original lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlProgramSystem.Construction.UniformControlProgramSystem.exists_common_carrier_lift {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {b c : ℕ} (hc : 0 < c) {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule c β}
    {X Y V W X' Y' V' W' : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f'] {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h'] {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} {L' : V'.IdealSheafData} {M' : W'.IdealSheafData}
    {D : β → V.IdealSheafData} {D' : β → V'.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M)
    (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X' f' J' Y' g' K') (Q' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V' h' L' W' k' M')
    (T : 𝒮.Program schedule h L D Q)
    (T' : 𝒮.Program schedule h' L' D' Q')
    (q : V ⟶ X) (r : W ⟶ Y) (q' : V' ⟶ X') (r' : W' ⟶ Y')
    (hcarrier : P.CarrierComparison Q q r) (hcarrier' : P'.CarrierComparison Q' q' r')
    (X0 V0 : Scheme) [IsIntegral X0] [IsLocallyNoetherian X0]
    [IsIntegral V0] [IsLocallyNoetherian V0] [CompactSpace V0] (hdV0 : topologicalKrullDim V0 ≤ d)
    (f0 : X0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h0 : V0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth h0] (J0 : X0.IdealSheafData)
    (L0 : V0.IdealSheafData) (hL0 : L0 ≠ ⊥) (D0 : β → V0.IdealSheafData) (q0 : V0 ⟶ X0)
    (a : X0 ⟶ X) [Etale a] (a' : X0 ⟶ X') [Etale a']
    (p : V0 ⟶ V) [Etale p] (p' : V0 ⟶ V') [Etale p']
    (haf : a ≫ f = f0) (haf' : a' ≫ f' = f0) (hph : p ≫ h = h0) (hph' : p' ≫ h' = h0)
    (hJ : J.comap a = J0) (hJ' : J'.comap a' = J0)
    (hL : L.comap p = L0) (hL' : L'.comap p' = L0)
    (hD : ∀ l, (D l).comap p = D0 l) (hD' : ∀ l, (D' l).comap p' = D0 l)
    (hpb : IsPullback p q0 q a) (hpb' : IsPullback p' q0 q' a') :
    ∃ (Y0 W0 : Scheme) (g0 : Y0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (k0 : W0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
      (K0 : Y0.IdealSheafData) (M0 : W0.IdealSheafData)
      (P0 : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X0 f0 J0 Y0 g0 K0) (Q0 : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V0 h0 L0 W0 k0 M0)
      (r0 : W0 ⟶ Y0) (t : Y0 ⟶ Y) (t' : Y0 ⟶ Y') (s : W0 ⟶ W) (s' : W0 ⟶ W'),
      𝒮.Program schedule h0 L0 D0 Q0 ∧
      P0.CarrierComparison Q0 q0 r0 ∧ P.EtaleComparison P0 a t ∧ P'.EtaleComparison P0 a' t' ∧
      Q.EtaleComparison Q0 p s ∧ Q'.EtaleComparison Q0 p' s' ∧
      IsPullback s r0 r t ∧ IsPullback s' r0 r' t' := by
  obtain ⟨W0, k0, M0, Q0, s, s', T0, hQ, hQ'⟩ := 𝒮.exists_common_etale_pullback hc T T' V0 hdV0
    h0 L0 hL0 D0 p p' hph hph' hL hL' hD hD'
  obtain ⟨Y0, g0, K0, P0, t, hP⟩ := P.exists_etale_pullback X0 f0 J0 a haf hJ
  obtain ⟨r0, hcarrier0, hpb0⟩ := P.carrierPullback Q q r hcarrier P0 Q0 q0 p s a t hP hQ hpb
  obtain ⟨t', hP', hpb0'⟩ := hcarrier'.exists_etaleComparison P' Q' q' r' P0 Q0 q0 r0 hcarrier0
    p' s' hQ' a' haf' hJ' hpb'
  exact ⟨Y0, W0, g0, k0, K0, M0, P0, Q0, r0, t, t', s, s', T0, hcarrier0, hP, hP', hQ, hQ', hpb0, hpb0'⟩

end

/-! Extract the common ambient prefix while keeping the coefficient and carrier construction opaque. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlProgramSystem.Construction.UniformControlProgramSystem.exists_common_ambient_program {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {b c : ℕ} (hc : 0 < c) {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule c β}
    {X Y V W X' Y' V' W' : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f'] {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h'] {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} {L' : V'.IdealSheafData} {M' : W'.IdealSheafData}
    {D : β → V.IdealSheafData} {D' : β → V'.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M)
    (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X' f' J' Y' g' K') (Q' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V' h' L' W' k' M')
    (T : 𝒮.Program schedule h L D Q)
    (T' : 𝒮.Program schedule h' L' D' Q')
    (q : V ⟶ X) (r : W ⟶ Y) (q' : V' ⟶ X') (r' : W' ⟶ Y')
    (hcarrier : P.CarrierComparison Q q r) (hcarrier' : P'.CarrierComparison Q' q' r')
    (X0 V0 : Scheme) [IsIntegral X0] [IsLocallyNoetherian X0]
    [IsIntegral V0] [IsLocallyNoetherian V0] [CompactSpace V0] (hdV0 : topologicalKrullDim V0 ≤ d)
    (f0 : X0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h0 : V0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth h0] (J0 : X0.IdealSheafData)
    (L0 : V0.IdealSheafData) (hL0 : L0 ≠ ⊥) (D0 : β → V0.IdealSheafData) (q0 : V0 ⟶ X0)
    (a : X0 ⟶ X) [Etale a] (a' : X0 ⟶ X') [Etale a']
    (p : V0 ⟶ V) [Etale p] (p' : V0 ⟶ V') [Etale p']
    (haf : a ≫ f = f0) (haf' : a' ≫ f' = f0) (hph : p ≫ h = h0) (hph' : p' ≫ h' = h0)
    (hJ : J.comap a = J0) (hJ' : J'.comap a' = J0)
    (hL : L.comap p = L0) (hL' : L'.comap p' = L0)
    (hD : ∀ l, (D l).comap p = D0 l) (hD' : ∀ l, (D' l).comap p' = D0 l)
    (hpb : IsPullback p q0 q a) (hpb' : IsPullback p' q0 q' a') :
    ∃ (Y0 : Scheme) (g0 : Y0 ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K0 : Y0.IdealSheafData)
      (P0 : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X0 f0 J0 Y0 g0 K0) (t : Y0 ⟶ Y) (t' : Y0 ⟶ Y'),
      P.EtaleComparison P0 a t ∧ P'.EtaleComparison P0 a' t' := by
  obtain ⟨Y0, W0, g0, k0, K0, M0, P0, Q0, r0, t, t', s, s', _, _, hP, hP', _⟩ :=
    𝒮.exists_common_carrier_lift hc P Q P' Q' T T' q r q' r' hcarrier hcarrier'
      X0 V0 hdV0 f0 h0 J0 L0 hL0 D0 q0 a a' p p' haf haf' hph hph'
      hJ hJ' hL hL' hD hD' hpb hpb'
  exact ⟨Y0, g0, K0, P0, t, t', hP, hP'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
