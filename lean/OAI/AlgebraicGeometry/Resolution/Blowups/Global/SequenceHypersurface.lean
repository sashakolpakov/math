import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Principality
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Sequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero

/-! # Sequence Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! A smooth Cartier hypersurface in the tangent ideal persists through an entire actual global control sequence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (n : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hp : J ≤ I ^ (n + 1)) (hH : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1 ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n := by
  have ht := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI 1 n
    (by simpa only [Nat.add_comm 1 n] using hp)
  rw [Nat.add_comm 1 n] at ht
  exact (HomogenizedTransform.Construction.globalBlowupControlledIdeal_mono I hI 1 hH).trans ht

def MonomialSequence.Construction.SmoothFixedControlSequence.transformIdeal {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (H : X.IdealSheafData) (c : ℕ) : T.endpoint.IdealSheafData := by
  revert H
  induction T with
  | terminal => intro H; exact H
  | blowup I hI hb hp hs hbl tail ih =>
      intro H
      exact ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI c)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.transformed_tangent_hypersurface
    {n : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) (H : X.IdealSheafData)
    (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hsmooth : Smooth (H.subschemeι ≫ f))
    (htangent : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) :
    T.transformIdeal H 1 ≠ ⊥ ∧ Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (T.transformIdeal H 1) ∧
      Smooth ((T.transformIdeal H 1).subschemeι ≫ (T.toBase ≫ f)) ∧
      T.transformIdeal H 1 ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) T.terminalIdeal n := by
  revert H
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _ H hH hl hsm htan
      change H ≠ ⊥ ∧ Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H ∧ Smooth (H.subschemeι ≫ (𝟙 Y ≫ g)) ∧
        H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) K n
      refine ⟨hH, hl, ?_, ?_⟩
      · simpa only [Category.id_comp] using hsm
      · rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g) K n]
        exact htan
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg H hH hl hsm htan
      let : Smooth g := hg
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (H.subschemeι ≫ g) := hsm
      have hHI : H ≤ I := htan.trans (OrderLocusPreservation.Construction.global_tangent_le_permissible_center g K I n hp)
      have hH' := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I H hI 1 hH
      have hl' := GlobalControlled.Principality.Construction.globalBlowupControlledIdeal_locallyPrincipal I H hI 1 (by simpa using hHI) hl
      have hsm' := SmoothHypersurfaceTransform.Construction.globalBlowup_smooth_controlled_hypersurface g I H hI hH hl hHI
      have ht' := SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le g I K H hI n hp htan
      have h := ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1) hH' hl' hsm' ht'
      let L := tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1) 1
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth ((tail.toBase ≫ π) ≫ g) := by
        rw [Category.assoc]
        exact tail.endpoint_structure_smooth
      change L ≠ ⊥ ∧ Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf L ∧ Smooth (L.subschemeι ≫ ((tail.toBase ≫ π) ≫ g)) ∧
        L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ π) ≫ g) tail.terminalIdeal n
      refine ⟨h.1, h.2.1, ?_, ?_⟩
      · simpa only [Category.assoc] using h.2.2.1
      · rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
          (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _) tail.terminalIdeal n]
        exact h.2.2.2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
