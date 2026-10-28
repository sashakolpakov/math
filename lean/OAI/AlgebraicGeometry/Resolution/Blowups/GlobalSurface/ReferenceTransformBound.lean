import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Homogenization
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.BoundDecrease
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform

/-! # Reference Transform Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The canonical surface center decreases the coefficient bound of the original controlled ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_original_transform_bound
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas
      (GlobalBlowup.Data.Construction.globalBlowupToBase (A.surfaceCenter ℓ hb hd hlevel) (A.surfaceCenter_nonzero ℓ hb hd hlevel) ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (A.surfaceCenter ℓ hb hd hlevel)
        J (A.surfaceCenter_nonzero ℓ hb hd hlevel) (n + 1)) n) :
    ∀ i, (B.choice i).HasBound ℓ := by
  let I := A.surfaceCenter ℓ hb hd hlevel
  let hI : I ≠ ⊥ := A.surfaceCenter_nonzero ℓ hb hd hlevel
  let H := Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let g := π ≫ f
  let : Smooth g := A.surfaceCenter_isBlowupSmooth ℓ hb hd hlevel
  let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace π
  have hperm : H ≤ I ^ (n + 1) := (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_permissible_iff f I J n).mpr
    (A.surfaceCenter_isPermissible ℓ hb hd hlevel)
  have hH : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H (n + 1) = ⊤ := by
    have h := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f (Global.Homogenization.Construction.le_smoothHomogenizedIdealSheaf f J n) (n + 1)
    rw [hbound] at h
    exact top_le_iff.mp h
  let L := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI (n + 1)
  have hL : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g L (n + 1) = ⊤ :=
    Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f I H hI (n + 1) hperm hH
  obtain ⟨C⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas g L n hL
  have hC : ∀ i, (C.choice i).HasBound ℓ := A.surfaceCenter_homogenized_transform_bound ℓ hb hd hlevel C
  have hinterval := Global.HomogenizedTransform.Construction.global_homogenized_interval_preserved f I J H hI n
    (Global.Homogenization.Construction.le_smoothHomogenizedIdealSheaf f J n) le_rfl hperm
  exact (B.hasBound_iff_of_homogenized_interval C hinterval.2.1 hinterval.2.2 ℓ).mpr hC

end

end OAI.AlgebraicGeometry.Resolution.Blowups
