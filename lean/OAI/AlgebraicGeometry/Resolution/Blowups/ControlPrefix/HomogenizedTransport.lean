import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform

/-! # Homogenized Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Prefixes at different controls can record literally the same blowups at every stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (b c : ℕ) :
    {X Y : Scheme} → {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} → {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} →
    {J L : X.IdealSheafData} → {K M : Y.IdealSheafData} →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K → Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M → Prop
  | stop {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J L : X.IdealSheafData} :
      SameBlowups b c (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J)
        (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L X f L)
  | blowup {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
      (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hc : 0 < c)
      (hp : J ≤ I ^ b) (hq : L ≤ I ^ c)
      (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K}
      {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c) Y g M}
      (tail : SameBlowups b c P Q) :
      SameBlowups b c (.blowup I hI hb hp hs hbl P) (.blowup I hI hc hq hs hbl Q)

variable {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.toBase_eq (h : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) : P.toBase = Q.toBase := by
  induction h with
  | stop => rfl
  | blowup I hI hb hc hp hq hs hbl tail ih => exact congrArg (fun r => r ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.stepCount_eq (h : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) : P.stepCount = Q.stepCount := by
  induction h with
  | stop => rfl
  | blowup I hI hb hc hp hq hs hbl tail ih => exact congrArg (fun a : ℕ => a + 1) ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.uniformBoundaryCompatible (h : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) :
    ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
      P.uniformBoundaryCompatible β D → Q.uniformBoundaryCompatible β D := by
  induction h with
  | stop => intro β _ D hD; exact hD
  | blowup I hI hb hc hp hq hs hbl tail ih =>
      intro β _ D hD
      exact ⟨hD.1, ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hD.2⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.canonicalBoundary (h : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) :
    ∀ (β : Type) (D : β → X.IdealSheafData), HEq (P.canonicalBoundary D) (Q.canonicalBoundary D) := by
  induction h with
  | stop => intro β D; rfl
  | blowup I hI hb hc hp hq hs hbl tail ih =>
      intro β D
      exact ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.boundaryAtLength (h : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) (β : Type) (D : β → X.IdealSheafData)
    (N : ℕ) (hP : P.stepCount = N) (hQ : Q.stepCount = N) :
    P.boundaryAtLength D N hP = Q.boundaryAtLength D N hQ :=
  ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_eq_of_heq hP hQ _ _ (h.canonicalBoundary β D)

end

/-! A recorded prefix for a homogenized comparison ideal gives the same actual blowups for the original ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_homogenized_interval_same_blowups
    {n : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f L Y g K) :
    ∀ [Smooth f] (J : X.IdealSheafData), J ≤ L → L ≤ Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n →
      ∃ (J' : Y.IdealSheafData) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g J'),
        Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (n + 1) (n + 1) P Q ∧
          (letI : Smooth g := P.endpoint_smooth; J' ≤ K ∧ K ≤ Global.Homogenization.Construction.smoothHomogenizedIdealSheaf g J' n) := by
  induction P with
  | stop =>
      intro _ J hJL hLH
      exact ⟨J, .stop, .stop, hJL, hLH⟩
  | @blowup X hX hNX f L I hI hb hp hs hbl Y g K tail ih =>
      intro hf J hJL hLH
      let : Smooth f := hf
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      obtain ⟨hJ, hle, hupp⟩ := Global.HomogenizedTransform.Construction.global_homogenized_interval_preserved f I J L hI n hJL hLH hp
      obtain ⟨J', Q, same, hnext⟩ := ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) hle hupp
      exact ⟨J', .blowup I hI hb hJ hs hbl Q, .blowup I hI hb hb hp hJ hs hbl same, hnext⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_homogenized_interval_terminal_prefix
    {n : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f L Y g K)
    (J : X.IdealSheafData) (hJL : J ≤ L) (hLH : L ≤ Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n)
    (ht : letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤) :
    ∃ (J' : Y.IdealSheafData) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g J'),
      Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (n + 1) (n + 1) P Q ∧
        (letI : Smooth g := Q.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g J' n = ⊤) := by
  let : Smooth g := P.endpoint_smooth
  obtain ⟨J', Q, same, hle, hupp⟩ := P.exists_homogenized_interval_same_blowups J hJL hLH
  exact ⟨J', Q, same, (Global.Homogenization.Construction.smooth_homogenized_interval_tangent_eq g J' K n hle hupp).symm.trans ht⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
