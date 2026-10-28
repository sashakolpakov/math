import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.BoundDecrease
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Dimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Clearance

/-! # Bounded Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.BoundedSequence.Construction

noncomputable section

/-! Termination of the actual global surface process by its finite coefficient bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_bounded_surface_sequence (m : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [CompactSpace X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
      (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n),
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤ →
      (∀ i, (A.choice i).HasBound m) → topologicalKrullDim X ≤ 2 →
      Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) := by
  induction m with
  | zero =>
      intro X _ _ f _ J n A _ hb _
      have ht := A.terminal_of_uniform_bound_lt_factorial hb (Nat.factorial_pos (n + 1))
      exact ⟨.terminal (by simpa using ht)⟩
  | succ m ih =>
      intro X _ _ f _ J n A hbound hb hd
      classical
      by_cases ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤
      · exact ⟨.terminal (by simpa using ht)⟩
      have hlevel : (n + 1).factorial ≤ m + 1 := by
        by_contra h
        exact ht (A.terminal_of_uniform_bound_lt_factorial hb (by omega))
      let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      let hdA := A.chart_dimension_le 2 hd
      let I := A.surfaceCenter m hb hdA hlevel
      let hI : I ≠ ⊥ := A.surfaceCenter_nonzero m hb hdA hlevel
      let H := Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n
      have hperm : H ≤ I ^ (n + 1) := (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_permissible_iff f I J n).mpr
        (A.surfaceCenter_isPermissible m hb hdA hlevel)
      have hH : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H (n + 1) = ⊤ := by
        have h := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f (Global.Homogenization.Construction.le_smoothHomogenizedIdealSheaf f J n) (n + 1)
        rw [hbound] at h
        exact top_le_iff.mp h
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let g := π ≫ f
      let : Smooth g := A.surfaceCenter_isBlowupSmooth m hb hdA hlevel
      let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace π
      let L := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI (n + 1)
      have hL : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g L (n + 1) = ⊤ :=
        Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f I H hI (n + 1) hperm hH
      obtain ⟨B⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas g L n hL
      have hB : ∀ i, (B.choice i).HasBound m :=
        A.surfaceCenter_homogenized_transform_bound m hb hdA hlevel B
      have hdY : topologicalKrullDim (GlobalBlowup.Data.Construction.globalBlowup I hI) ≤ 2 := GlobalBlowup.Dimension.Construction.globalBlowup_dimension_le f I hI 2 hd
      obtain ⟨tail⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup I hI) g L n B hL hB hdY
      let T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f H :=
        .blowup I hI (Nat.succ_pos n) hperm (A.surfaceCenter_isSmooth m hb hdA hlevel) inferInstance tail
      exact T.of_homogenization J

theorem exists_global_surface_fixed_control_sequence
    (X : Scheme) [IsIntegral X] [CompactSpace X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (n : ℕ) (hd : topologicalKrullDim X ≤ 2)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤) :
    Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨A⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas f J n hbound
  let I := A.center
  let hI : I ≠ ⊥ := A.center_ne_bot
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let : IsIso π := A.center_blowup_isIso
  let : Smooth (π ≫ f) := inferInstance
  let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨B, _, m, hb⟩ := A.exists_bounded_atlas_after_component_blowup hbound
  have hL := Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f I J hI (n + 1) A.center_permissible hbound
  have hdY : topologicalKrullDim (GlobalBlowup.Data.Construction.globalBlowup I hI) ≤ 2 := GlobalBlowup.Dimension.Construction.globalBlowup_dimension_le f I hI 2 hd
  obtain ⟨tail⟩ := exists_global_bounded_surface_sequence m (GlobalBlowup.Data.Construction.globalBlowup I hI) (π ≫ f)
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n B hL hb hdY
  exact ⟨.blowup I hI (Nat.succ_pos n) A.center_permissible A.center_smooth inferInstance tail⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.BoundedSequence.Construction
