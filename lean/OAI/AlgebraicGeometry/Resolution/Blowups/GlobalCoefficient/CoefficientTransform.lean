import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Sums
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PowerScaling
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform

/-! # Coefficient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientTransform.Construction

noncomputable section

/-! Weighted coefficient transforms on the actual blowup of a global carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

/-- The coefficient ideal transforms as the weighted sum of the separately
controlled ambient differential ideals, restricted by the actual comparison map. -/
theorem globalBlowup_coefficient_transform_eq (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (q : Y ⟶ X) (I J : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥)
    (b : ℕ) (hp : J ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (I.comap q) (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q) hY b.factorial =
      ⨆ j : Fin b, ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I
        (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val) hI (b - j.val)).comap
          (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap q I hI hY)) ^ WeightedCoefficientIdeal.Construction.coefficientWeight b j := by
  have hd (j : Fin b) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val ≤ I ^ (b - j.val) :=
    Global.DifferentialPermissibility.Construction.smoothDifferentialIdealSheaf_le_pow f I J (b - j.val) j.val
      (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hp)
  have hdY (j : Fin b) : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap q ≤
      (I.comap q) ^ (b - j.val) := by
    have h := Scheme.IdealSheafData.comap_mono q (hd j)
    change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap q ≤ (I ^ (b - j.val)).comap q at h
    rwa [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow] at h
  have hpY (j : Fin b) : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap q) ^ WeightedCoefficientIdeal.Construction.coefficientWeight b j ≤
      (I.comap q) ^ b.factorial := by
    have h := pow_le_pow_left' (hdY j) (WeightedCoefficientIdeal.Construction.coefficientWeight b j)
    rwa [← pow_mul, WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control] at h
  rw [CoefficientSheaf.Construction.smoothCoefficientIdealSheaf, GlobalControlled.Sums.Construction.globalBlowupControlledIdeal_iSup _ _ hY b.factorial hpY]
  apply congrArg iSup
  funext j
  rw [← WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control b j,
    Global.PowerScaling.Construction.globalBlowupControlledIdeal_pow _ _ hY (b - j.val) (WeightedCoefficientIdeal.Construction.coefficientWeight b j) (hdY j),
    GlobalBlowup.MapControlledIdeal.Construction.globalBlowupMap_controlledIdeal q I _ hI hY (b - j.val) (hd j)]

/-- The retained coefficient transform lies below the newly computed intrinsic
coefficient ideal on the transformed carrier. -/
theorem globalBlowup_coefficient_transform_le (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (q : Y ⟶ X) (I J : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (b : ℕ) (hp : J ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (I.comap q) (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q) hY b.factorial ≤
      CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap q I hI hY) := by
  rw [globalBlowup_coefficient_transform_eq f q I J hI hY b hp]
  apply iSup_mono
  intro j
  apply pow_le_pow_left'
  apply Scheme.IdealSheafData.comap_mono
  have h := Global.DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI (b - j.val) j.val
    (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hp)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientTransform.Construction
