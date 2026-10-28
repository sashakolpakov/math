import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Sequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup

/-! # Sequence Order Complement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! A whole actual control sequence preserves the original open set below its order threshold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem MonomialSequence.Construction.SmoothFixedControlSequence.toBase_orderComplement_isIso
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (hb : 0 < b) :
    IsIso (T.toBase ∣_ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support.compl) := by
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _
      exact inferInstanceAs (IsIso (𝟙 Y ∣_ _))
  | @blowup Y hY hN g K I hI hb' hp hs hbl tail ih =>
      intro hg
      let : Smooth g := hg
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth (π ≫ g) := hbl
      let O := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1)).support.compl
      let O' := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ g)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I K hI b) (b - 1)).support.compl
      let : IsIso (tail.toBase ∣_ O') := ih
      have hpre : π ⁻¹ᵁ O ≤ O' := OrderLocusPreservation.Construction.globalBlowup_orderComplement_preimage_le g I K hI b hb hp
      let : IsIso (tail.toBase ∣_ π ⁻¹ᵁ O) := Blowup.Complement.Construction.isIso_restrict_of_le tail.toBase hpre
      let : IsIso (π ∣_ O) := OrderLocusPreservation.Construction.globalBlowup_preserves_orderComplement g I K hI b hb hp
      change IsIso ((tail.toBase ≫ π) ∣_ O)
      exact (morphismRestrict_comp tail.toBase π O).symm ▸
        (inferInstance : IsIso ((tail.toBase ∣_ π ⁻¹ᵁ O) ≫ (π ∣_ O)))

def MonomialSequence.Construction.SmoothFixedControlSequence.blowupSmoothCenter
    {b : ℕ} {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f))
    (tail : MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)) : MonomialSequence.Construction.SmoothFixedControlSequence b X f J := by
  let : Smooth (I.subschemeι ≫ f) := hs
  exact .blowup I hI hb hp hs (SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI) tail

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
