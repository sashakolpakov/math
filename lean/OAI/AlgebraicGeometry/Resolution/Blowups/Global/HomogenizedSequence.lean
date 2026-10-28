import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialSequence

/-! # Homogenized Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! A finite global sequence for a homogenized comparison ideal also resolves the original marked ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem MonomialSequence.Construction.SmoothFixedControlSequence.of_homogenized_interval {n : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    [Smooth f] {L : X.IdealSheafData} (T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f L)
    (J : X.IdealSheafData) (hJL : J ≤ L) (hLH : L ≤ Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) :
    Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) := by
  revert J
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _ J hJK hKH
      have he := Homogenization.Construction.smooth_homogenized_interval_tangent_eq g J K n hJK hKH
      have ht' : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by simpa using ht
      exact ⟨.terminal (by simpa using he.symm.trans ht')⟩
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg J hJK hKH
      let : Smooth g := hg
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      have h := HomogenizedTransform.Construction.global_homogenized_interval_preserved g I J K hI n hJK hKH hp
      obtain ⟨rest⟩ := ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) h.2.1 h.2.2
      exact ⟨.blowup I hI hb h.1 hs hbl rest⟩

theorem MonomialSequence.Construction.SmoothFixedControlSequence.of_homogenization {n : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    [Smooth f] (J : X.IdealSheafData)
    (T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n)) :
    Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) :=
  T.of_homogenized_interval J (Homogenization.Construction.le_smoothHomogenizedIdealSheaf f J n) le_rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
