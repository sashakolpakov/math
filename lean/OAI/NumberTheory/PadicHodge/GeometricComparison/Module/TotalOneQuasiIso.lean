import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleCriterion

/-! # Total One Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneQuasiIso.ModuleTotalHOneQuasiIso

noncomputable section

/-! The original first-quadrant total map is an isomorphism on H¹
when the first three column maps have the required low-degree isomorphisms. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneCoordinates.ModuleTotalOneCoordinates OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneMap.ModuleTotalOneMap
universe u v
variable {R : Type u} [CommRing R]
  {B C : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  [B.HasTotal (.up ℕ)] [C.HasTotal (.up ℕ)] (f : B ⟶ C)

theorem quasiIsoAt (h0 : QuasiIso (f.f 0)) (h1 : QuasiIso (f.f 1))
    (h2 : QuasiIsoAt (f.f 2) 0) :
    QuasiIsoAt (HomologicalComplex₂.total.map f (.up ℕ)) 1 := by
  let := h1
  apply (quasiIsoAt_iff' (HomologicalComplex₂.total.map f (.up ℕ)) 0 1 2
    (by simp) (by simp)).mpr
  apply QuasiIsoCycleCriterion.ModuleQuasiIsoCycleCriterion.quasiIso
  · change ∀ z : (C.total (.up ℕ)).X 1, ((C.total (.up ℕ)).d 1 2).hom z = 0 →
      ∃ x : (B.total (.up ℕ)).X 1, ((B.total (.up ℕ)).d 1 2).hom x = 0 ∧
        ∃ b : (C.total (.up ℕ)).X 0,
          ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom x - z =
            ((C.total (.up ℕ)).d 0 1).hom b
    intro z hz
    obtain ⟨a, c, ha, hac, hc, b, hb₀, hb₁⟩ := BicomplexOne.BicomplexOneCycleLifts.cycle_lift f h0 h1 h2
      (TotalOneCoordinates.ModuleTotalOneCoordinates.first C z) (TotalOneCoordinates.ModuleTotalOneCoordinates.second C z) (TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_first C z hz) (TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_mixed C z hz) (TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_second C z hz)
    refine ⟨TotalOneCoordinates.ModuleTotalOneCoordinates.one B (a, c), TotalOneCoordinates.ModuleTotalOneCoordinates.one_cycle B a c ha hac hc, TotalOneCoordinates.ModuleTotalOneCoordinates.zero C b, ?_⟩
    rw [TotalOneMap.ModuleTotalOneMap.map_one, TotalOneCoordinates.ModuleTotalOneCoordinates.boundary]
    calc
      _ = TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component f 0 1 a, BicomplexLow.BicomplexLowDegree.component f 1 0 c) -
          TotalOneCoordinates.ModuleTotalOneCoordinates.one C (TotalOneCoordinates.ModuleTotalOneCoordinates.first C z, TotalOneCoordinates.ModuleTotalOneCoordinates.second C z) := by rw [TotalOneCoordinates.ModuleTotalOneCoordinates.one_coordinates]
      _ = TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.component f 0 1 a - TotalOneCoordinates.ModuleTotalOneCoordinates.first C z, BicomplexLow.BicomplexLowDegree.component f 1 0 c - TotalOneCoordinates.ModuleTotalOneCoordinates.second C z) :=
        (map_sub (TotalOneCoordinates.ModuleTotalOneCoordinates.one C) _ _).symm
      _ = _ := by rw [hb₀, hb₁]
  · change ∀ z : (B.total (.up ℕ)).X 1, ((B.total (.up ℕ)).d 1 2).hom z = 0 →
      ∀ b : (C.total (.up ℕ)).X 0,
        ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom z = ((C.total (.up ℕ)).d 0 1).hom b →
          ∃ a : (B.total (.up ℕ)).X 0, ((B.total (.up ℕ)).d 0 1).hom a = z
    intro z hz b hb
    let b₀ := ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat C) 0 0 0).hom b
    have hboundary : ((HomologicalComplex₂.total.map f (.up ℕ)).f 1).hom z =
        TotalOneCoordinates.ModuleTotalOneCoordinates.one C (BicomplexLow.BicomplexLowDegree.vertical C 0 0 b₀, BicomplexLow.BicomplexLowDegree.horizontal C 0 0 b₀) := by
      calc
        _ = ((C.total (.up ℕ)).d 0 1).hom b := hb
        _ = ((C.total (.up ℕ)).d 0 1).hom (TotalOneCoordinates.ModuleTotalOneCoordinates.zero C b₀) :=
          congrArg _ (TotalOneCoordinates.ModuleTotalOneCoordinates.zero_coordinate C b).symm
        _ = _ := TotalOneCoordinates.ModuleTotalOneCoordinates.boundary C b₀
    have hx : BicomplexLow.BicomplexLowDegree.component f 0 1 (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) = BicomplexLow.BicomplexLowDegree.vertical C 0 0 b₀ := by
      simpa only [TotalOneMap.ModuleTotalOneMap.first_map, TotalOneCoordinates.ModuleTotalOneCoordinates.first_one] using congrArg (TotalOneCoordinates.ModuleTotalOneCoordinates.first C) hboundary
    have hy : BicomplexLow.BicomplexLowDegree.component f 1 0 (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) = BicomplexLow.BicomplexLowDegree.horizontal C 0 0 b₀ := by
      simpa only [TotalOneMap.ModuleTotalOneMap.second_map, TotalOneCoordinates.ModuleTotalOneCoordinates.second_one] using congrArg (TotalOneCoordinates.ModuleTotalOneCoordinates.second C) hboundary
    obtain ⟨a, ha₀, ha₁⟩ := BicomplexOne.BicomplexOneCycleLifts.boundary_lift f h0 inferInstance
      (TotalOneCoordinates.ModuleTotalOneCoordinates.first B z) (TotalOneCoordinates.ModuleTotalOneCoordinates.second B z) (TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_first B z hz) (TotalOneCoordinates.ModuleTotalOneCoordinates.cycle_mixed B z hz) b₀ hx hy
    refine ⟨TotalOneCoordinates.ModuleTotalOneCoordinates.zero B a, ?_⟩
    rw [TotalOneCoordinates.ModuleTotalOneCoordinates.boundary, ha₀, ha₁, TotalOneCoordinates.ModuleTotalOneCoordinates.one_coordinates]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneQuasiIso.ModuleTotalHOneQuasiIso
