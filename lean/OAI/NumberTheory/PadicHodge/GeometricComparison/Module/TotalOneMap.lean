import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates

/-! # Total One Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneMap.ModuleTotalOneMap

noncomputable section

/-! Degree-one coordinate formulas for the original map of total complexes. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates.ModuleTotalOneCoordinates
universe u v
variable {R : Type u} [CommRing R]
  {B C : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  [B.HasTotal (.up ℕ)] [C.HasTotal (.up ℕ)] (f : B ⟶ C)

theorem map_zero (b : (B.X 0).X 0) :
    ((HomologicalComplex₂.total.map f (.up ℕ)).f 0).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.zero B b) =
      TotalOneCoordinates.ModuleTotalOneCoordinates.zero C (BicomplexLow.BicomplexLowDegree.component f 0 0 b) :=
  congrArg (fun g => g.hom b) (HomologicalComplex₂.ιTotal_map B C f (.up ℕ) 0 0 0 rfl)

theorem map_one (x : (B.X 0).X 1) (y : (B.X 1).X 0) :
    ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.one B (x, y)) =
      TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component f 0 1 x, BicomplexLow.BicomplexLowDegree.component f 1 0 y) := by
  have h01 := congrArg (fun g => g.hom x) (HomologicalComplex₂.ιTotal_map B C f (.up ℕ) 0 1 1 rfl)
  have h10 := congrArg (fun g => g.hom y) (HomologicalComplex₂.ιTotal_map B C f (.up ℕ) 1 0 1 rfl)
  change ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom (_ + _) = _
  rw [map_add]
  exact congrArg₂ (· + ·) h01 h10

theorem first_map (z : (B.total (.up ℕ)).X 1) :
    TotalOneCoordinates.ModuleTotalOneCoordinates.first C (((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom z) =
      BicomplexLow.BicomplexLowDegree.component f 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) := by
  calc
    _ = TotalOneCoordinates.ModuleTotalOneCoordinates.first C (((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom
      (TotalOneCoordinates.ModuleTotalOneCoordinates.one B (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z, TotalOneCoordinates.ModuleTotalOneCoordinates.second B z))) := by rw [TotalOneCoordinates.ModuleTotalOneCoordinates.one_coordinates]
    _ = _ := by rw [map_one, TotalOneCoordinates.ModuleTotalOneCoordinates.first_one]

theorem second_map (z : (B.total (.up ℕ)).X 1) :
    TotalOneCoordinates.ModuleTotalOneCoordinates.second C (((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom z) =
      BicomplexLow.BicomplexLowDegree.component f 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) := by
  calc
    _ = TotalOneCoordinates.ModuleTotalOneCoordinates.second C (((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom
      (TotalOneCoordinates.ModuleTotalOneCoordinates.one B (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z, TotalOneCoordinates.ModuleTotalOneCoordinates.second B z))) := by rw [TotalOneCoordinates.ModuleTotalOneCoordinates.one_coordinates]
    _ = _ := by rw [map_one, TotalOneCoordinates.ModuleTotalOneCoordinates.second_one]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneMap.ModuleTotalOneMap
