import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.HomologyBoundaryEquality
import Mathlib.Algebra.Homology.Homotopy

/-! # Total Homotopy One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalHomotopyOne.ModuleTotalHomotopyHOne

noncomputable section

/-! A horizontal cochain homotopy induces equality on H-one of the
original first-quadrant total complexes, by their actual cycle coordinates. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates.ModuleTotalOneCoordinates
universe u v
variable {R : Type u} [CommRing R]
  {B C : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  {f g : B ⟶ C} (h : Homotopy f g)

theorem row_zero (j : ℕ) (x : (B.X 0).X j) : BicomplexLow.BicomplexLowDegree.component f 0 j x - BicomplexLow.BicomplexLowDegree.component g 0 j x =
    ((h.hom 1 0).f j).hom (BicomplexLow.BicomplexLowDegree.horizontal B 0 j x) := by
  have hh := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
    prevD_eq_zero h.hom 0 (by simp), add_zero] at hh
  have hx := congrArg (fun q => (q.f j).hom x) hh
  exact sub_eq_iff_eq_add.mpr hx

theorem row_one (j : ℕ) (x : (B.X 1).X j) : BicomplexLow.BicomplexLowDegree.component f 1 j x - BicomplexLow.BicomplexLowDegree.component g 1 j x =
    ((h.hom 2 1).f j).hom (BicomplexLow.BicomplexLowDegree.horizontal B 1 j x) +
      BicomplexLow.BicomplexLowDegree.horizontal C 0 j (((h.hom 1 0).f j).hom x) := by
  have hh := h.comm 1
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 1 2 from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl)] at hh
  have hx := congrArg (fun q => (q.f j).hom x) hh
  exact sub_eq_iff_eq_add.mpr hx

variable [B.HasTotal (.up ℕ)] [C.HasTotal (.up ℕ)]

omit [C.HasTotal (.up ℕ)] in
theorem first_boundary (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) :
    BicomplexLow.BicomplexLowDegree.component f 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) - BicomplexLow.BicomplexLowDegree.component g 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) =
      BicomplexLow.BicomplexLowDegree.vertical C 0 0 (((h.hom 1 0).f 0).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) := by
  rw [row_zero h, TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_mixed B z hz]
  exact (congrArg (fun q => q.hom (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) ((h.hom 1 0).comm 0 1)).symm

omit [C.HasTotal (.up ℕ)] in
theorem second_boundary (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) :
    BicomplexLow.BicomplexLowDegree.component f 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) - BicomplexLow.BicomplexLowDegree.component g 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) =
      BicomplexLow.BicomplexLowDegree.horizontal C 0 0 (((h.hom 1 0).f 0).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) := by
  rw [row_one h, TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_second B z hz, map_zero, zero_add]

theorem boundary (z : (B.total (.up ℕ)).X 1)
    (hz : ((B.total (.up ℕ)).d 1 2).hom z = 0) :
    ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom z -
      ((HomologicalComplex₂.total.map g (.up ℕ)).f 1).hom z =
        ((C.total (.up ℕ)).d 0 1).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.zero C (((h.hom 1 0).f 0).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z))) := by
  calc
    _ = TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component f 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z), BicomplexLow.BicomplexLowDegree.component f 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) -
        TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component g 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z), BicomplexLow.BicomplexLowDegree.component g 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) := by
      rw [← TotalOneMap.ModuleTotalOneMap.map_one, ← TotalOneMap.ModuleTotalOneMap.map_one, TotalOneCoordinates.ModuleTotalOneCoordinates.one_coordinates]
    _ = TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component f 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) - BicomplexLow.BicomplexLowDegree.component g 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z),
        BicomplexLow.BicomplexLowDegree.component f 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) - BicomplexLow.BicomplexLowDegree.component g 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)) := (map_sub (TotalOneCoordinates.ModuleTotalOneCoordinates.one C) _ _).symm
    _ = _ := by rw [first_boundary h z hz, second_boundary h z hz, TotalOneCoordinates.ModuleTotalOneCoordinates.boundary]

include h in
theorem homology : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (.up ℕ)) 1 =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map g (.up ℕ)) 1 := by
  let F := HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) 0 1 2
  have he : ShortComplex.homologyMap (F.map (HomologicalComplex₂.total.map f (.up ℕ))) =
      ShortComplex.homologyMap (F.map (HomologicalComplex₂.total.map g (.up ℕ))) := by
    apply HomologyBoundaryEquality.ModuleHomologyBoundaryEquality.homology
    intro z hz
    exact ⟨TotalOneCoordinates.ModuleTotalOneCoordinates.zero C (((h.hom 1 0).f 0).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z)), boundary h z hz⟩
  let e := HomologicalComplex.homologyFunctorIso' (ModuleCat.{v} R) (.up ℕ) 0 1 2 (by simp) (by simp)
  apply (cancel_mono (e.app (C.total (.up ℕ))).hom).mp
  exact (e.hom.naturality (HomologicalComplex₂.total.map f (.up ℕ))).trans
    ((congrArg (fun q => (e.app (B.total (.up ℕ))).hom ≫ q) he).trans
      (e.hom.naturality (HomologicalComplex₂.total.map g (.up ℕ))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalHomotopyOne.ModuleTotalHomotopyHOne
