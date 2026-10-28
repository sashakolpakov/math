import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ProgramHeadInvariance
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent

/-! # Symmetric Control Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

/-! Full symmetry of actual control prefixes persists past isomorphic steps whose controlled ideal is the pulled-back input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
  ∀ (q : X ⟶ X) [Etale q], q ≫ f = f → J.comap q = J → ∃ r : Y ⟶ Y, P.EtaleComparison P q r

theorem Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem.etaleSymmetric_of_unit_boundary
    {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule b β} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : 𝒮.Program schedule f J (fun _ : β => ⊤) P) : P.EtaleSymmetric := by
  intro q _ hf hJ
  exact 𝒮.comparison H H q hf hJ (fun _ => Scheme.IdealSheafData.comap_top q)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.head_center_comap
    {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (H : (blowup I hI hb hp hs hbl tail).EtaleSymmetric)
    (q : X ⟶ X) [Etale q] (hf : q ≫ f = f) (hJ : J.comap q = J) : I.comap q = I := by
  obtain ⟨r, hr⟩ := H q hf hJ
  obtain ⟨_, _, _, he, _⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    I hI hb hp hs hbl tail I hI hb hp hs hbl tail q r).mp hr
  exact he

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.tail_of_isomorphic_step
    {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (H : (blowup I hI hb hp hs hbl tail).EtaleSymmetric)
    [IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)]
    (htransform : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b = J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) :
    tail.EtaleSymmetric := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  intro q _ hf hJ
  let a := inv π ≫ q ≫ π
  let : Etale a := inferInstance
  have hπa : π ≫ a = q ≫ π := by simp [a, ← Category.assoc]
  have ha : a ≫ f = f := by
    calc
      a ≫ f = inv π ≫ (q ≫ (π ≫ f)) := by simp only [a, Category.assoc]
      _ = inv π ≫ (π ≫ f) := by rw [hf]
      _ = f := by simp
  have hJa : J.comap a = J := by
    have h : (J.comap a).comap π = J.comap π := by
      rw [← Scheme.IdealSheafData.comap_comp, hπa, Scheme.IdealSheafData.comap_comp,
        ← htransform, hJ]
    exact le_antisymm ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ π).mp h.le)
      ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ π).mp h.ge)
  obtain ⟨r, hr⟩ := H a ha hJa
  obtain ⟨_, _, _, he, ht⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    I hI hb hp hs hbl tail I hI hb hp hs hbl tail a r).mp hr
  have hmap : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I he hI hI = q := by
    apply (cancel_mono π).mp
    exact (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over a I I he hI hI).trans hπa
  exact ⟨r, hmap ▸ ht⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
