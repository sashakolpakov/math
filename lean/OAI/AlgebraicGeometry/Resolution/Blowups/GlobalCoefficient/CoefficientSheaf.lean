import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction

/-! # Coefficient Sheaf -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf.Construction

noncomputable section

/-! Intrinsic weighted coefficient ideals on an actual global carrier, without a choice of hypersurface equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def smoothCoefficientIdealSheaf {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) : Y.IdealSheafData :=
  ⨆ j : Fin b, ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap q) ^ WeightedCoefficientIdeal.Construction.coefficientWeight b j

theorem smoothCoefficientIdealSheaf_comap {X Y Z : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) (g : Z ⟶ Y) :
    (smoothCoefficientIdealSheaf f J b q).comap g = smoothCoefficientIdealSheaf f J b (g ≫ q) := by
  simp only [smoothCoefficientIdealSheaf, Affine.KernelSums.Construction.idealSheaf_comap_iSup, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow,
    Scheme.IdealSheafData.comap_comp]

theorem smoothCoefficientIdealSheaf_mono {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    {J K : X.IdealSheafData} (hJK : J ≤ K) (b : ℕ) (q : Y ⟶ X) :
    smoothCoefficientIdealSheaf f J b q ≤ smoothCoefficientIdealSheaf f K b q := by
  apply iSup_mono
  intro j
  exact pow_le_pow_left' (Scheme.IdealSheafData.comap_mono q (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f hJK j.val)) _

theorem smoothCoefficientIdealSheaf_le_of_order {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) (hJ : J ≤ I ^ b) :
    smoothCoefficientIdealSheaf f J b q ≤ (I.comap q) ^ b.factorial := by
  apply iSup_le
  intro j
  have hd := Global.DifferentialPermissibility.Construction.smoothDifferentialIdealSheaf_le_pow f I J (b - j.val) j.val
    (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)
  have h := Scheme.IdealSheafData.comap_mono q hd
  change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J j.val).comap q ≤ (I ^ (b - j.val)).comap q at h
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow] at h
  have hp := pow_le_pow_left' h (WeightedCoefficientIdeal.Construction.coefficientWeight b j)
  rwa [← pow_mul, WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control] at hp

theorem smoothCoefficientIdealSheaf_comap_open_square
    {X Y X' Y' : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) (q' : Y' ⟶ X')
    (j : X' ⟶ X) [IsOpenImmersion j] (l : Y' ⟶ Y) (hcomm : l ≫ q = q' ≫ j) :
    (smoothCoefficientIdealSheaf f J b q).comap l =
      smoothCoefficientIdealSheaf (j ≫ f) (J.comap j) b q' := by
  rw [smoothCoefficientIdealSheaf_comap]
  simp only [smoothCoefficientIdealSheaf, hcomm, Scheme.IdealSheafData.comap_comp,
    Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf.Construction
