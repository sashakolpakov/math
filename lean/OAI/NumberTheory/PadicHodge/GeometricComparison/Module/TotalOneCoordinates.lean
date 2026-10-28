import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary

/-! # Total One Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates.ModuleTotalOneCoordinates

noncomputable section

/-! Degree-zero and degree-one module coordinates of the original total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree
universe u v
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [B.HasTotal (.up ℕ)]

def zero : (B.X 0).X 0 →ₗ[R] (B.total (.up ℕ)).X 0 :=
  (B.ιTotal (.up ℕ) 0 0 0 rfl).hom

def one : (B.X 0).X 1 × (B.X 1).X 0 →ₗ[R] (B.total (.up ℕ)).X 1 :=
  (B.ιTotal (.up ℕ) 0 1 1 rfl).hom.comp (LinearMap.fst R _ _) +
    (B.ιTotal (.up ℕ) 1 0 1 rfl).hom.comp (LinearMap.snd R _ _)

def first : (B.total (.up ℕ)).X 1 →ₗ[R] (B.X 0).X 1 := ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1).hom

def second : (B.total (.up ℕ)).X 1 →ₗ[R] (B.X 1).X 0 := ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1).hom

theorem first_one (x : (B.X 0).X 1) (y : (B.X 1).X 0) : first B (one B (x, y)) = x := by
  change ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1).hom (_ + _) = x
  rw [map_add]
  change (B.ιTotal (.up ℕ) 0 1 1 rfl ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1).hom x +
    (B.ιTotal (.up ℕ) 1 0 1 rfl ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 1 1).hom y = x
  simp

theorem second_one (x : (B.X 0).X 1) (y : (B.X 1).X 0) : second B (one B (x, y)) = y := by
  change ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1).hom (_ + _) = y
  rw [map_add]
  change (B.ιTotal (.up ℕ) 0 1 1 rfl ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1).hom x +
    (B.ιTotal (.up ℕ) 1 0 1 rfl ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 1 0 1).hom y = y
  simp

theorem one_coordinates (z : (B.total (.up ℕ)).X 1) : one B (first B z, second B z) = z :=
  congrArg (fun g => g.hom z) (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.totalUpNat_one_decomposition B)

theorem zero_coordinate (z : (B.total (.up ℕ)).X 0) :
    zero B (((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 0 0).hom z) = z :=
  congrArg (fun g => g.hom z) (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.totalUpNat_zero_decomposition B)

theorem one_injective : Function.Injective (one B) := by
  rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ h
  apply Prod.ext
  · simpa only [first_one] using congrArg (first B) h
  · simpa only [second_one] using congrArg (second B) h

theorem boundary (b : (B.X 0).X 0) :
    ((B.total (.up ℕ)).d 0 1).hom (zero B b) =
      one B (BicomplexLow.BicomplexLowDegree.vertical B 0 0 b, BicomplexLow.BicomplexLowDegree.horizontal B 0 0 b) := by
  have h := congrArg (fun g => g.hom b) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 0 0)
  simpa [zero, one, BicomplexLow.BicomplexLowDegree.vertical, BicomplexLow.BicomplexLowDegree.horizontal, add_comm] using h

theorem cycle_first (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) : BicomplexLow.BicomplexLowDegree.vertical B 0 1 (first B z) = 0 := by
  have h := congrArg (fun g => g.hom z) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero B 1)
  change ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 2 2).hom (((B.total (.up ℕ)).d 1 2).hom z) =
    BicomplexLow.BicomplexLowDegree.vertical B 0 1 (first B z) at h
  rw [hz, map_zero] at h
  exact h.symm

theorem cycle_mixed (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) :
    BicomplexLow.BicomplexLowDegree.horizontal B 0 1 (first B z) = BicomplexLow.BicomplexLowDegree.vertical B 1 0 (second B z) := by
  have h := congrArg (fun g => g.hom z) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_interior B 0 0)
  have h' : BicomplexLow.BicomplexLowDegree.horizontal B 0 1 (first B z) - BicomplexLow.BicomplexLowDegree.vertical B 1 0 (second B z) = 0 := by
    simpa [first, second, BicomplexLow.BicomplexLowDegree.horizontal, BicomplexLow.BicomplexLowDegree.vertical, hz, Units.smul_def, sub_eq_add_neg] using h.symm
  exact sub_eq_zero.mp h'

theorem cycle_second (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) : BicomplexLow.BicomplexLowDegree.horizontal B 1 0 (second B z) = 0 := by
  have h := congrArg (fun g => g.hom z) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right B 1)
  change ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 2 0 2).hom (((B.total (.up ℕ)).d 1 2).hom z) =
    BicomplexLow.BicomplexLowDegree.horizontal B 1 0 (second B z) at h
  rw [hz, map_zero] at h
  exact h.symm

theorem one_cycle (x : (B.X 0).X 1) (y : (B.X 1).X 0)
    (hx : BicomplexLow.BicomplexLowDegree.vertical B 0 1 x = 0) (hxy : BicomplexLow.BicomplexLowDegree.horizontal B 0 1 x = BicomplexLow.BicomplexLowDegree.vertical B 1 0 y)
    (hy : BicomplexLow.BicomplexLowDegree.horizontal B 1 0 y = 0) : ((B.total (.up ℕ)).d 1 2).hom (one B (x, y)) = 0 := by
  have h01 := congrArg (fun g => g.hom x) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 0 1)
  have h10 := congrArg (fun g => g.hom y) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat B) 1 0)
  change ((B.total (.up ℕ)).d 1 2).hom (_ + _) = 0
  rw [map_add]
  dsimp only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h01 h10
  rw [h01, h10]
  simp only [pow_zero, pow_one, one_smul, Units.smul_def, Units.val_neg,
    Units.val_one, neg_one_zsmul, ModuleCat.hom_add, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.neg_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  change ((B.ιTotal (.up ℕ) 1 1 2 rfl).hom (BicomplexLow.BicomplexLowDegree.horizontal B 0 1 x) +
      (B.ιTotal (.up ℕ) 0 2 2 rfl).hom (BicomplexLow.BicomplexLowDegree.vertical B 0 1 x)) +
    ((B.ιTotal (.up ℕ) 2 0 2 rfl).hom (BicomplexLow.BicomplexLowDegree.horizontal B 1 0 y) +
      -(B.ιTotal (.up ℕ) 1 1 2 rfl).hom (BicomplexLow.BicomplexLowDegree.vertical B 1 0 y)) = 0
  rw [hx, hy, hxy, map_zero, map_zero]
  abel

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates.ModuleTotalOneCoordinates
