import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisconnectedDivisorDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SimultaneousMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Divisor Intersection -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorIntersection

noncomputable section

section

/-! Descent of both divisor-intersection inputs in every dimension and codimension,
using the actual open and closed integral components. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace DisconnectedDescent

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem intersection_congr (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a a' : X.RationalDimensionCycle 1) (b b' : X.RationalDimensionCycle (k + 1))
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b b')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a' b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + (k + 1)) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' b') := by
  apply (Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m (1 + (k + 1)) _ _).mpr
  intro C
  let := Component.Image.component_relativeDimension X m C
  rw [Component.Bilinear.restrict_bilinear X m C 1 (k + 1) a b,
    Component.Bilinear.restrict_bilinear X m C 1 (k + 1) a' b']
  exact DivisorDescent.intersection_congr (X.componentVariety C).presentation m k _ _ _ _
    ((Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m 1 a a').mp ha C)
    ((Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m (k + 1) b b').mp hb C)
    (DisconnectedDivisorDescent.meetProperly_restrict X C 1 (k + 1) a b hp)
    (DisconnectedDivisorDescent.meetProperly_restrict X C 1 (k + 1) a' b' hp')

end DisconnectedDescent

end

section

/-! The Chow value of divisor intersection is independent of
representatives and bilinear in every dimension and positive codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry
open scoped Classical

namespace Value

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ) [SmoothOfRelativeDimension m X.structureMap]

def moved (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) : X.RationalDimensionCycle 1 :=
  (Divisor.SimultaneousMoving.move_pair X m (k + 1) a b b).choose

theorem moved_spec (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a (moved X m k a b) ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) (moved X m k a b) b :=
  by
  have h := (Divisor.SimultaneousMoving.move_pair X m (k + 1) a b b).choose_spec
  exact ⟨h.1, h.2.1⟩

def value (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) : ProperCycleLinearity.ChowQ X (1 + (k + 1)) :=
  ProperCycleLinearity.cycleToChowQ X (1 + (k + 1)) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) (moved X m k a b) b)

theorem value_of_proper (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1))
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b) : value X m k a b = ProperCycleLinearity.cycleToChowQ X (1 + (k + 1)) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b) := by
  apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (1 + (k + 1)) _ _).mpr
  exact DisconnectedDescent.intersection_congr X m k _ a b b
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X 1 (moved_spec X m k a b).1) (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) b)
    (moved_spec X m k a b).2 hp

theorem value_congr (a a' : X.RationalDimensionCycle 1) (b b' : X.RationalDimensionCycle (k + 1))
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b b') :
    value X m k a b = value X m k a' b' := by
  apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (1 + (k + 1)) _ _).mpr
  exact DisconnectedDescent.intersection_congr X m k _ _ b b'
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X 1 (moved_spec X m k a b).1)
      (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 1 ha (moved_spec X m k a' b').1)) hb
    (moved_spec X m k a b).2 (moved_spec X m k a' b').2

theorem value_add_right (a : X.RationalDimensionCycle 1) (b c : X.RationalDimensionCycle (k + 1)) :
    value X m k a (b + c) = value X m k a b + value X m k a c := by
  obtain ⟨u, hu, hub, huc⟩ := Divisor.SimultaneousMoving.move_pair X m (k + 1) a b c
  have hv (v : X.RationalDimensionCycle (k + 1)) := value_congr X m k a u v v hu (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) v)
  rw [hv (b + c), hv b, hv c, value_of_proper X m k u (b + c) (ProperCycleLinearity.add_right X 1 (k + 1) u b c hub huc),
    value_of_proper X m k u b hub, value_of_proper X m k u c huc, map_add, map_add]

theorem value_smul_right (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) (q : ℚ) :
    value X m k a (q • b) = q • value X m k a b := by
  let u := moved X m k a b
  have hu := moved_spec X m k a b
  have hv (v : X.RationalDimensionCycle (k + 1)) := value_congr X m k a u v v hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) v)
  rw [hv (q • b), hv b, value_of_proper X m k u (q • b) (ProperCycleLinearity.smul_right X 1 (k + 1) u b q hu.2),
    value_of_proper X m k u b hu.2, map_smul, map_smul]

theorem value_add_left (a b : X.RationalDimensionCycle 1) (c : X.RationalDimensionCycle (k + 1)) :
    value X m k (a + b) c = value X m k a c + value X m k b c := by
  let u := moved X m k a c
  let v := moved X m k b c
  have hu := moved_spec X m k a c
  have hv := moved_spec X m k b c
  have huv : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) (u + v) c := by
    intro D hD A hA
    rcases Finset.mem_union.mp (Finsupp.support_add hD) with hD | hD
    · exact hu.2 D hD A hA
    · exact hv.2 D hD A hA
  have he : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 (a + b) (u + v) := by
    have h := Submodule.add_mem (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1) hu.1 hv.1
    change (a - u) + (b - v) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1 at h
    change (a + b) - (u + v) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    convert h using 1
    abel
  rw [value_congr X m k (a + b) (u + v) c c he (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) c),
    value_congr X m k a u c c hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) c),
    value_congr X m k b v c c hv.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) c),
    value_of_proper X m k (u + v) c huv, value_of_proper X m k u c hu.2, value_of_proper X m k v c hv.2,
    map_add, LinearMap.add_apply, map_add]

theorem value_smul_left (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) (q : ℚ) :
    value X m k (q • a) b = q • value X m k a b := by
  let u := moved X m k a b
  have hu := moved_spec X m k a b
  have hqu : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) (q • u) b := fun D hD A hA => hu.2 D (Finsupp.support_smul hD) A hA
  have he : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 (q • a) (q • u) := by
    change q • a - q • u ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ hu.1
  rw [value_congr X m k (q • a) (q • u) b b he (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) b),
    value_congr X m k a u b b hu.1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) b),
    value_of_proper X m k (q • u) b hqu, value_of_proper X m k u b hu.2,
    map_smul, LinearMap.smul_apply, map_smul]

end Value

end

/-! The exact bilinear map for divisor intersection in every dimension
and positive codimension, with the native relation as its singleton graph. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry

namespace Positive

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorIntersection.Value

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ) [SmoothOfRelativeDimension m X.structureMap]

def cycleMap : X.RationalDimensionCycle 1 →ₗ[ℚ] X.RationalDimensionCycle (k + 1) →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + (k + 1)) :=
  LinearMap.mk₂ ℚ (Value.value X m k) (Value.value_add_left X m k) (fun q a b => Value.value_smul_left X m k a b q)
    (Value.value_add_right X m k) (fun q a b => Value.value_smul_right X m k a b q)

theorem cycleMap_relation_right (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1))
    (hb : b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (k + 1)) : cycleMap X m k a b = 0 := by
  have h : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b 0 := by simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, sub_zero] using hb
  exact (Value.value_congr X m k a a b 0 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 a) h).trans ((cycleMap X m k a).map_zero)

def onCycles : X.RationalDimensionCycle 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X (k + 1) →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + (k + 1)) where
  toFun a := (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (k + 1)).liftQ (cycleMap X m k a) (fun b hb => cycleMap_relation_right X m k a b hb)
  map_add' a a' := by
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (k + 1) β
    change Value.value X m k (a + a') b = Value.value X m k a b + Value.value X m k a' b
    exact Value.value_add_left X m k a a' b
  map_smul' q a := by
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (k + 1) β
    change Value.value X m k (q • a) b = q • Value.value X m k a b
    exact Value.value_smul_left X m k a b q

def chowMap : ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X (k + 1) →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + (k + 1)) :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).liftQ (onCycles X m k) (by
    intro a ha
    apply LinearMap.ext
    intro β
    obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (k + 1) β
    change Value.value X m k a b = 0
    have h : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a 0 := by simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, sub_zero] using ha
    exact (Value.value_congr X m k a 0 b b h (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) b)).trans
      (congrArg (fun F : X.RationalDimensionCycle (k + 1) →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + (k + 1)) => F b) (cycleMap X m k).map_zero))

theorem chowMap_mk (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1)) :
    chowMap X m k (ProperCycleLinearity.cycleToChowQ X 1 a) (ProperCycleLinearity.cycleToChowQ X (k + 1) b) = Value.value X m k a b := rfl

theorem representsIntersection_iff (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1))
    (c : X.RationalDimensionCycle (1 + (k + 1))) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X 1 (k + 1) a b c ↔
      ProperCycleLinearity.cycleToChowQ X (1 + (k + 1)) c = chowMap X m k (ProperCycleLinearity.cycleToChowQ X 1 a) (ProperCycleLinearity.cycleToChowQ X (k + 1) b) := by
  rw [chowMap_mk]
  constructor
  · rintro ⟨a', b', c', ha, hb, hp, hc⟩
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X (1 + (k + 1)) c c').mpr hc]
    have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 (k + 1) hp (Supports.ProperCycle.intersectionBilinear_isProper X m 1 (k + 1) a' b' hp.1)
    rw [he, ← Value.value_of_proper X m k a' b' hp.1]
    exact Value.value_congr X m k a' a b' b (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X 1 ha) (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X (k + 1) hb)
  · intro h
    refine ⟨Value.moved X m k a b, b, Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) (Value.moved X m k a b) b,
      (Value.moved_spec X m k a b).1, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (k + 1) b,
      Supports.ProperCycle.intersectionBilinear_isProper X m 1 (k + 1) _ b (Value.moved_spec X m k a b).2, ?_⟩
    exact (ProperCycleLinearity.cycleToChowQ_eq_iff X (1 + (k + 1)) _ _).mp h

theorem chowIntersection_eq_singleton (a : ProperCycleLinearity.ChowQ X 1) (b : ProperCycleLinearity.ChowQ X (k + 1)) :
    ProperCycleLinearity.chowIntersection X 1 (k + 1) a b = {chowMap X m k a b} := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (k + 1) b
  ext c
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (1 + (k + 1)) c
  rw [ProperCycleLinearity.chowIntersection_mk_iff, Set.mem_singleton_iff, representsIntersection_iff X m k]

include m in
theorem chowIntersection_map_exists :
    ∃ I : ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X (k + 1) →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + (k + 1)),
      ∀ a b, ProperCycleLinearity.chowIntersection X 1 (k + 1) a b = {I a b} :=
  ⟨chowMap X m k, chowIntersection_eq_singleton X m k⟩

end Positive

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorIntersection
