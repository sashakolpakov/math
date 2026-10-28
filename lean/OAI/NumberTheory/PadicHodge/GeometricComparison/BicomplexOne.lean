import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow

/-! # Bicomplex One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexOne.BicomplexOneCycleLifts

noncomputable section

/-! A comparison of the first three columns lifts total degree-one cycles
and detects total degree-one boundaries. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexLow.BicomplexLowDegree
universe u v
variable {R : Type u} [CommRing R]
  {B C : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)} (f : B ⟶ C)

theorem cycle_lift (h0 : QuasiIso (f.f 0)) (h1 : QuasiIso (f.f 1))
    (h2 : QuasiIsoAt (f.f 2) 0)
    (x : (C.X 0).X 1) (y : (C.X 1).X 0)
    (hx : BicomplexLow.BicomplexLowDegree.vertical C 0 1 x = 0)
    (hxy : BicomplexLow.BicomplexLowDegree.horizontal C 0 1 x = BicomplexLow.BicomplexLowDegree.vertical C 1 0 y)
    (hy : BicomplexLow.BicomplexLowDegree.horizontal C 1 0 y = 0) :
    ∃ a : (B.X 0).X 1, ∃ c : (B.X 1).X 0,
      BicomplexLow.BicomplexLowDegree.vertical B 0 1 a = 0 ∧ BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a = BicomplexLow.BicomplexLowDegree.vertical B 1 0 c ∧
      BicomplexLow.BicomplexLowDegree.horizontal B 1 0 c = 0 ∧ ∃ b : (C.X 0).X 0,
        BicomplexLow.BicomplexLowDegree.component f 0 1 a - x = BicomplexLow.BicomplexLowDegree.vertical C 0 0 b ∧
        BicomplexLow.BicomplexLowDegree.component f 1 0 c - y = BicomplexLow.BicomplexLowDegree.horizontal C 0 0 b := by
  let := h0
  let := h1
  obtain ⟨a, ha, b, hb⟩ :=
    CochainLow.CochainLowDegreeLifts.one_cycle_lift (f.f 0) inferInstance x hx
  change BicomplexLow.BicomplexLowDegree.vertical B 0 1 a = 0 at ha
  have hfa : BicomplexLow.BicomplexLowDegree.component f 0 1 a = BicomplexLow.BicomplexLowDegree.vertical C 0 0 b + x := sub_eq_iff_eq_add.mp hb
  let y' := BicomplexLow.BicomplexLowDegree.horizontal C 0 0 b + y
  have hu : BicomplexLow.BicomplexLowDegree.vertical B 1 1 (BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a) = 0 := by
    rw [BicomplexLow.BicomplexLowDegree.vertical_horizontal, ha, map_zero]
  have hfu : BicomplexLow.BicomplexLowDegree.component f 1 1 (BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a) = BicomplexLow.BicomplexLowDegree.vertical C 1 0 y' := by
    rw [BicomplexLow.BicomplexLowDegree.component_horizontal, hfa, map_add, ← BicomplexLow.BicomplexLowDegree.vertical_horizontal, hxy, ← map_add]
  obtain ⟨z, hz⟩ := CochainLow.CochainLowDegreeLifts.one_boundary_lift (f.f 1) inferInstance
    (BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a) hu y' hfu
  change BicomplexLow.BicomplexLowDegree.vertical B 1 0 z = BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a at hz
  have hclosed : BicomplexLow.BicomplexLowDegree.vertical C 1 0 (BicomplexLow.BicomplexLowDegree.component f 1 0 z - y') = 0 := by
    rw [map_sub, ← BicomplexLow.BicomplexLowDegree.component_vertical, hz, hfu, sub_self]
  obtain ⟨w, hw, hfw⟩ := CochainLow.CochainLowDegreeLifts.zero_cycle_lift (f.f 1) inferInstance
    (BicomplexLow.BicomplexLowDegree.component f 1 0 z - y') hclosed
  change BicomplexLow.BicomplexLowDegree.vertical B 1 0 w = 0 at hw
  let c := z - w
  have hc : BicomplexLow.BicomplexLowDegree.vertical B 1 0 c = BicomplexLow.BicomplexLowDegree.horizontal B 0 1 a := by
    dsimp [c]
    rw [map_sub, hw, sub_zero]
    exact hz
  have hfc : BicomplexLow.BicomplexLowDegree.component f 1 0 c = y' := by
    change BicomplexLow.BicomplexLowDegree.component f 1 0 (z - w) = y'
    rw [map_sub, show BicomplexLow.BicomplexLowDegree.component f 1 0 w = BicomplexLow.BicomplexLowDegree.component f 1 0 z - y' from hfw]
    abel
  have hvhc : BicomplexLow.BicomplexLowDegree.vertical B 2 0 (BicomplexLow.BicomplexLowDegree.horizontal B 1 0 c) = 0 := by
    rw [BicomplexLow.BicomplexLowDegree.vertical_horizontal, hc, BicomplexLow.BicomplexLowDegree.horizontal_horizontal]
  have hfhc : BicomplexLow.BicomplexLowDegree.component f 2 0 (BicomplexLow.BicomplexLowDegree.horizontal B 1 0 c) = 0 := by
    rw [BicomplexLow.BicomplexLowDegree.component_horizontal, hfc]
    dsimp [y']
    rw [map_add, BicomplexLow.BicomplexLowDegree.horizontal_horizontal, hy, add_zero]
  have hhc := CochainLow.CochainLowDegreeLifts.zero_cycle_injective (f.f 2) h2
    (BicomplexLow.BicomplexLowDegree.horizontal B 1 0 c) hvhc hfhc
  refine ⟨a, c, ha, hc.symm, hhc, b, hb, ?_⟩
  rw [hfc]
  exact add_sub_cancel_right _ _

theorem boundary_lift (h0 : QuasiIso (f.f 0)) (h1 : QuasiIsoAt (f.f 1) 0)
    (x : (B.X 0).X 1) (y : (B.X 1).X 0)
    (hx : BicomplexLow.BicomplexLowDegree.vertical B 0 1 x = 0)
    (hxy : BicomplexLow.BicomplexLowDegree.horizontal B 0 1 x = BicomplexLow.BicomplexLowDegree.vertical B 1 0 y)
    (b : (C.X 0).X 0)
    (hbx : BicomplexLow.BicomplexLowDegree.component f 0 1 x = BicomplexLow.BicomplexLowDegree.vertical C 0 0 b)
    (hby : BicomplexLow.BicomplexLowDegree.component f 1 0 y = BicomplexLow.BicomplexLowDegree.horizontal C 0 0 b) :
    ∃ a : (B.X 0).X 0, BicomplexLow.BicomplexLowDegree.vertical B 0 0 a = x ∧ BicomplexLow.BicomplexLowDegree.horizontal B 0 0 a = y := by
  let := h0
  obtain ⟨a, ha⟩ := CochainLow.CochainLowDegreeLifts.one_boundary_lift (f.f 0) inferInstance x hx b hbx
  change BicomplexLow.BicomplexLowDegree.vertical B 0 0 a = x at ha
  have hclosed : BicomplexLow.BicomplexLowDegree.vertical C 0 0 (b - BicomplexLow.BicomplexLowDegree.component f 0 0 a) = 0 := by
    rw [map_sub, ← BicomplexLow.BicomplexLowDegree.component_vertical, ha, hbx, sub_self]
  obtain ⟨c, hc, hfc⟩ := CochainLow.CochainLowDegreeLifts.zero_cycle_lift (f.f 0) inferInstance
    (b - BicomplexLow.BicomplexLowDegree.component f 0 0 a) hclosed
  change BicomplexLow.BicomplexLowDegree.vertical B 0 0 c = 0 at hc
  have hzero : BicomplexLow.BicomplexLowDegree.vertical B 1 0 (y - BicomplexLow.BicomplexLowDegree.horizontal B 0 0 (a + c)) = 0 := by
    rw [map_sub, BicomplexLow.BicomplexLowDegree.vertical_horizontal, map_add, ha, hc, add_zero, hxy, sub_self]
  have hfzero : BicomplexLow.BicomplexLowDegree.component f 1 0 (y - BicomplexLow.BicomplexLowDegree.horizontal B 0 0 (a + c)) = 0 := by
    rw [map_sub, BicomplexLow.BicomplexLowDegree.component_horizontal, map_add]
    change BicomplexLow.BicomplexLowDegree.component f 1 0 y - BicomplexLow.BicomplexLowDegree.horizontal C 0 0 (BicomplexLow.BicomplexLowDegree.component f 0 0 a + BicomplexLow.BicomplexLowDegree.component f 0 0 c) = 0
    rw [show BicomplexLow.BicomplexLowDegree.component f 0 0 c = b - BicomplexLow.BicomplexLowDegree.component f 0 0 a from hfc]
    have hadd : BicomplexLow.BicomplexLowDegree.component f 0 0 a + (b - BicomplexLow.BicomplexLowDegree.component f 0 0 a) = b := by abel
    rw [hadd, hby, sub_self]
  have hz := CochainLow.CochainLowDegreeLifts.zero_cycle_injective (f.f 1) h1
    (y - BicomplexLow.BicomplexLowDegree.horizontal B 0 0 (a + c)) hzero hfzero
  refine ⟨a + c, ?_, (sub_eq_zero.mp hz).symm⟩
  rw [map_add, ha, hc, add_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexOne.BicomplexOneCycleLifts
