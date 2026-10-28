import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceOrderComplement
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialFiltration

/-! # Sequence Differential Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Lower differential-order complements survive whole actual fixed-control sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem SequenceDifferentialPullback.Construction.globalBlowup_differential_total_le_controlled
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b r : ℕ) (hr : r ≤ b) (hp : J ≤ I ^ b)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) r := by
  have he : b - r + r = b := Nat.sub_add_cancel hr
  have h := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI (b - r) r (he.symm ▸ hp)
  rw [he] at h
  exact (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r) (b - r)
    (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).trans h

theorem MonomialSequence.Construction.SmoothFixedControlSequence.differential_total_le_terminal
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (r : ℕ) (hr : r ≤ b) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).comap T.toBase ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) T.terminalIdeal r := by
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _
      change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K r).comap (𝟙 Y) ≤
        Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) K r
      rw [Scheme.IdealSheafData.comap_id]
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g)]
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg
      let : Smooth g := hg
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth (π ≫ g) := hbl
      let : Smooth ((tail.toBase ≫ π) ≫ g) := by
        rw [Category.assoc]
        exact tail.endpoint_structure_smooth
      have hstep := SequenceDifferentialPullback.Construction.globalBlowup_differential_total_le_controlled g I K hI b r hr hp
      have h := (Scheme.IdealSheafData.comap_mono tail.toBase hstep).trans ih
      change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K r).comap (tail.toBase ≫ π) ≤
        Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ π) ≫ g) tail.terminalIdeal r
      rw [Scheme.IdealSheafData.comap_comp]
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
        (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _)]
      exact h

theorem MonomialSequence.Construction.SmoothFixedControlSequence.orderComplement_preimage_le_terminal
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (r : ℕ) (hr : r ≤ b) :
    T.toBase ⁻¹ᵁ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).support.compl ≤
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) T.terminalIdeal r).support.compl := by
  have h := Scheme.IdealSheafData.support_antitone (T.differential_total_le_terminal r hr)
  rw [Scheme.IdealSheafData.support_comap] at h
  intro x hx hh
  exact hx (h hh)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.toBase_lowerOrderComplement_isIso
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (r : ℕ) (hr : r < b) :
    IsIso (T.toBase ∣_ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).support.compl) := by
  let : IsIso (T.toBase ∣_ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support.compl) :=
    T.toBase_orderComplement_isIso (by omega)
  apply Blowup.Complement.Construction.isIso_restrict_of_le T.toBase (V := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support.compl)
  have h := Scheme.IdealSheafData.support_antitone
    (DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_monotone_order f J (show r ≤ b - 1 by omega))
  intro x hx hh
  exact hx (h hh)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
