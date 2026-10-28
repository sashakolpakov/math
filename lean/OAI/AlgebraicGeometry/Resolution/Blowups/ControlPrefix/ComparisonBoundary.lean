import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Comparison Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The specified comparison map preserves the canonical and fixed-length endpoint boundary families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.canonicalBoundary
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r →
      ∀ (β : Type) (D : β → X.IdealSheafData) (E : β → V.IdealSheafData),
      (∀ l, (D l).comap q = E l) →
      HEq (fun l => (P.canonicalBoundary D l).comap r) (Q.canonicalBoundary E) := by
  induction P with
  | stop =>
      intro V W h k L M Q q r hc β D E hD
      cases Q with
      | stop =>
          obtain ⟨_, _, _, hr⟩ := hc
          subst r
          exact heq_of_eq (funext hD)
      | blowup => exact False.elim hc
  | blowup I hI hb hp hs hbl tail ih =>
      intro V W h k L M Q q r hc β D E hD
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨hq, _, _, he, ht⟩ := hc
          let : Etale q := hq
          let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC
          have hD' : ∀ l, (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap q' =
              CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC E l := by
            intro l
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale q I C he hI hC D l]
            have hE : (fun l => (D l).comap q) = E := funext hD
            rw [hE]
          exact ih rest q' r ht (Option β)
            (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC E) hD'

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.boundaryAtLength
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData}
    (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y)
    (hc : P.EtaleComparison Q q r) (β : Type) (D : β → X.IdealSheafData) (E : β → V.IdealSheafData)
    (hD : ∀ l, (D l).comap q = E l) (N : ℕ) (hPN : P.stepCount = N) (hQN : Q.stepCount = N) :
    (fun l => (P.boundaryAtLength D N hPN l).comap r) = Q.boundaryAtLength E N hQN := by
  have ht := hc.canonicalBoundary P Q q r β D E hD
  unfold Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength
  exact (ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_map hPN (P.canonicalBoundary D) (fun I : Y.IdealSheafData => I.comap r)).trans
    (ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_eq_of_heq hPN hQN _ _ ht)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
