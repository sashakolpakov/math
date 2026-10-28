import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.NonzeroPersistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface

/-! # Sequence Coefficient Persistence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Integral coefficient hypersurfaces with nonzero coefficients persist through actual global control sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr {X Y : Scheme}
    (f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] [Smooth g] (hfg : f = g)
    (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) :
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q = GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf g J b q := by
  subst g
  rfl

/-- An existing actual sequence retains an integral maximal-contact carrier
and a nonzero intrinsic coefficient ideal at every endpoint. -/
theorem MonomialSequence.Construction.SmoothFixedControlSequence.transformed_integral_coefficient_hypersurface
    {n : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) (H : X.IdealSheafData)
    [IsIntegral H.subscheme] (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H)
    (hsmooth : Smooth (H.subschemeι ≫ f)) (htangent : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥) :
    IsIntegral (T.transformIdeal H 1).subscheme ∧
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (T.toBase ≫ f) T.terminalIdeal (n + 1)
        (T.transformIdeal H 1).subschemeι ≠ ⊥ := by
  revert H
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _ H hInt _ _ _ _ hC
      change IsIntegral H.subscheme ∧
        GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (𝟙 Y ≫ g) K (n + 1) H.subschemeι ≠ ⊥
      refine ⟨hInt, ?_⟩
      rw [SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g)]
      exact hC
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg H hInt hH hl hsm ht hC
      let : Smooth g := hg
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (H.subschemeι ≫ g) := hsm
      have hHI : H ≤ I := ht.trans (OrderLocusPreservation.Construction.global_tangent_le_permissible_center g K I n hp)
      have hIH := GlobalCoefficient.NonzeroPersistence.Construction.coefficient_nonzero_center_pullback_ne_bot g I K H (n + 1) (Nat.succ_pos n) hp hC
      let H' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
      let : IsIntegral H'.subscheme :=
        SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_controlled_isIntegral g I H hI hH hl hHI hIH
      have hH' : H' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I H hI 1 hH
      have hl' := GlobalControlled.Principality.Construction.globalBlowupControlledIdeal_locallyPrincipal I H hI 1 (by simpa using hHI) hl
      have hsm' := SmoothHypersurfaceTransform.Construction.globalBlowup_smooth_controlled_hypersurface g I H hI hH hl hHI
      have ht' := SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le g I K H hI n hp ht
      have hC' := GlobalCoefficient.NonzeroPersistence.Construction.globalBlowup_smooth_hypersurface_coefficient_ne_bot g I K H hI hH hl hHI
        (n + 1) (Nat.succ_pos n) hp hC
      have h := ih H' hH' hl' hsm' ht' hC'
      let L := tail.transformIdeal H' 1
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth ((tail.toBase ≫ π) ≫ g) := by
        rw [Category.assoc]
        exact tail.endpoint_structure_smooth
      change IsIntegral L.subscheme ∧
        GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf ((tail.toBase ≫ π) ≫ g) tail.terminalIdeal (n + 1) L.subschemeι ≠ ⊥
      refine ⟨h.1, ?_⟩
      rw [SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
        (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _)]
      exact h.2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
