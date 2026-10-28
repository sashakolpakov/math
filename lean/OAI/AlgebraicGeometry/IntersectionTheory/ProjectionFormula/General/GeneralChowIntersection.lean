import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.SimultaneousMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # General Chow Intersection -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection

noncomputable section

section

/-! The Chow value of native intersection is independent of
representatives and bilinear in every pair of codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry
open scoped Classical

namespace Value

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]

def moved (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) : X.RationalDimensionCycle p :=
  (SimultaneousMoving.pair X m p q a b b).choose

theorem moved_spec (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a (moved X m p q a b) ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (moved X m p q a b) b :=
  by
  have h := (SimultaneousMoving.pair X m p q a b b).choose_spec
  exact ⟨h.1, h.2.1⟩

def value (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) : ProperCycleLinearity.ChowQ X (p + q) :=
  ProperCycleLinearity.cycleToChowQ X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q (moved X m p q a b) b)

theorem value_of_proper (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) : value X m p q a b = ProperCycleLinearity.cycleToChowQ X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) := by
  apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (p + q) _ _).mpr
  exact ProperDescent.intersection_congr X m p q _ a b b
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p (moved_spec X m p q a b).1) (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b)
    (moved_spec X m p q a b).2 hp

theorem value_congr (a a' : X.RationalDimensionCycle p) (b b' : X.RationalDimensionCycle q)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b') :
    value X m p q a b = value X m p q a' b' := by
  apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (p + q) _ _).mpr
  exact ProperDescent.intersection_congr X m p q _ _ b b'
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p (moved_spec X m p q a b).1)
      (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p ha (moved_spec X m p q a' b').1)) hb
    (moved_spec X m p q a b).2 (moved_spec X m p q a' b').2

theorem value_add_right (a : X.RationalDimensionCycle p) (b c : X.RationalDimensionCycle q) :
    value X m p q a (b + c) = value X m p q a b + value X m p q a c := by
  obtain ⟨u, hu, hub, huc⟩ := SimultaneousMoving.pair X m p q a b c
  have hv (v : X.RationalDimensionCycle q) := value_congr X m p q a u v v hu (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q v)
  rw [hv (b + c), hv b, hv c, value_of_proper X m p q u (b + c) (ProperCycleLinearity.add_right X p q u b c hub huc),
    value_of_proper X m p q u b hub, value_of_proper X m p q u c huc, map_add, map_add]

theorem value_smul_right (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) (r : ℚ) :
    value X m p q a (r • b) = r • value X m p q a b := by
  let u := moved X m p q a b
  have hu := moved_spec X m p q a b
  have hv (v : X.RationalDimensionCycle q) := value_congr X m p q a u v v hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q v)
  rw [hv (r • b), hv b, value_of_proper X m p q u (r • b) (ProperCycleLinearity.smul_right X p q u b r hu.2),
    value_of_proper X m p q u b hu.2, map_smul, map_smul]

theorem value_add_left (a b : X.RationalDimensionCycle p) (c : X.RationalDimensionCycle q) :
    value X m p q (a + b) c = value X m p q a c + value X m p q b c := by
  let u := moved X m p q a c
  let v := moved X m p q b c
  have hu := moved_spec X m p q a c
  have hv := moved_spec X m p q b c
  have huv : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (u + v) c := by
    intro D hD A hA
    rcases Finset.mem_union.mp (Finsupp.support_add hD) with hD | hD
    · exact hu.2 D hD A hA
    · exact hv.2 D hD A hA
  have he : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (a + b) (u + v) := by
    have h := Submodule.add_mem (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p) hu.1 hv.1
    change (a - u) + (b - v) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p at h
    change (a + b) - (u + v) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
    convert h using 1
    abel
  rw [value_congr X m p q (a + b) (u + v) c c he (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q c),
    value_congr X m p q a u c c hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q c),
    value_congr X m p q b v c c hv.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q c),
    value_of_proper X m p q (u + v) c huv, value_of_proper X m p q u c hu.2, value_of_proper X m p q v c hv.2,
    map_add, LinearMap.add_apply, map_add]

theorem value_smul_left (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) (r : ℚ) :
    value X m p q (r • a) b = r • value X m p q a b := by
  let u := moved X m p q a b
  have hu := moved_spec X m p q a b
  have hqu : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (r • u) b := fun D hD A hA => hu.2 D (Finsupp.support_smul hD) A hA
  have he : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (r • a) (r • u) := by
    change r • a - r • u ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ hu.1
  rw [value_congr X m p q (r • a) (r • u) b b he (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b),
    value_congr X m p q a u b b hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b),
    value_of_proper X m p q (r • u) b hqu, value_of_proper X m p q u b hu.2,
    map_smul, LinearMap.smul_apply, map_smul]

end Value

end

/-! The exact bilinear Chow intersection map in every pair of
codimensions, with the native geometric relation as its singleton graph. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection.Value

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]

def cycleMap : X.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q) :=
  LinearMap.mk₂ ℚ (Value.value X m p q) (Value.value_add_left X m p q) (fun r a b => Value.value_smul_left X m p q a b r)
    (Value.value_add_right X m p q) (fun r a b => Value.value_smul_right X m p q a b r)

theorem cycleMap_relation_right (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (hb : b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q) : cycleMap X m p q a b = 0 := by
  have h : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b 0 := by simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, sub_zero] using hb
  exact (Value.value_congr X m p q a a b 0 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p a) h).trans ((cycleMap X m p q a).map_zero)

def onCycles : X.RationalDimensionCycle p →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q) where
  toFun a := (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q).liftQ (cycleMap X m p q a) (fun b hb => cycleMap_relation_right X m p q a b hb)
  map_add' a a' := by
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q β
    change Value.value X m p q (a + a') b = Value.value X m p q a b + Value.value X m p q a' b
    exact Value.value_add_left X m p q a a' b
  map_smul' r a := by
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q β
    change Value.value X m p q (r • a) b = r • Value.value X m p q a b
    exact Value.value_smul_left X m p q a b r

def chowMap : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q) :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).liftQ (onCycles X m p q) (by
    intro a ha
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q β
    change Value.value X m p q a b = 0
    have h : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a 0 := by simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, sub_zero] using ha
    exact (Value.value_congr X m p q a 0 b b h (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b)).trans
      (congrArg (fun F : X.RationalDimensionCycle q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q) => F b) (cycleMap X m p q).map_zero))

theorem chowMap_mk (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X q b) = Value.value X m p q a b := rfl

theorem representsIntersection_iff (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c ↔
      ProperCycleLinearity.cycleToChowQ X (p + q) c = chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X q b) := by
  rw [chowMap_mk]
  constructor
  · rintro ⟨a', b', c', ha, hb, hp, hc⟩
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X (p + q) c c').mpr hc]
    have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p q hp (Supports.ProperCycle.intersectionBilinear_isProper X m p q a' b' hp.1)
    rw [he, ← Value.value_of_proper X m p q a' b' hp.1]
    exact Value.value_congr X m p q a' a b' b (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p ha) (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X q hb)
  · intro h
    refine ⟨Value.moved X m p q a b, b, Supports.ProperCycle.intersectionBilinear X m p q (Value.moved X m p q a b) b,
      (Value.moved_spec X m p q a b).1, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b,
      Supports.ProperCycle.intersectionBilinear_isProper X m p q _ b (Value.moved_spec X m p q a b).2, ?_⟩
    exact (ProperCycleLinearity.cycleToChowQ_eq_iff X (p + q) _ _).mp h

theorem chowIntersection_eq_singleton (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) :
    ProperCycleLinearity.chowIntersection X p q a b = {chowMap X m p q a b} := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  ext c
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (p + q) c
  rw [ProperCycleLinearity.chowIntersection_mk_iff, Set.mem_singleton_iff, representsIntersection_iff X m p q]

include m in
theorem chowIntersection_map_exists :
    ∃ I : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q),
      ∀ a b, ProperCycleLinearity.chowIntersection X p q a b = {I a b} :=
  ⟨chowMap X m p q, chowIntersection_eq_singleton X m p q⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection
