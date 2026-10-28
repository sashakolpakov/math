import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Program Head Invariance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Full program naturality forces the actual first center to be invariant under every étale symmetry of the marked input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlProgramSystem.Construction.UniformControlProgramSystem.head_center_comap
    {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d) {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule b β} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (H : 𝒮.Program schedule f J D (.blowup I hI hb hp hs hbl tail))
    (q : X ⟶ X) [Etale q] (hf : q ≫ f = f) (hJ : J.comap q = J)
    (hD : ∀ l, (D l).comap q = D l) : I.comap q = I := by
  obtain ⟨r, hr⟩ := 𝒮.comparison H H q hf hJ hD
  obtain ⟨_, _, _, he, _⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    I hI hb hp hs hbl tail I hI hb hp hs hbl tail q r).mp hr
  exact he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
