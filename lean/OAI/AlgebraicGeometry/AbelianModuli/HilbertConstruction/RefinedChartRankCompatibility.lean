import Mathlib.CategoryTheory.Category.Basic

/-! # Refined Chart Rank Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedChartRankCompatibility

/-! The rank map on a refined chart follows from its three original
commuting triangles. -/

open _root_.CategoryTheory
universe v u

theorem compositeRankMap_from_chart
    {C : Type u} [Category.{v} C] {V M F J G B K : C}
    (a : V ⟶ M) (u : M ⟶ G) (c : V ⟶ G) (p : G ⟶ B)
    (q : M ⟶ F) (h : F ⟶ J) (t : J ⟶ B) (r : B ⟶ K) (s : J ⟶ K)
    (hb : a ≫ u = c) (hu : u ≫ p = (q ≫ h) ≫ t) (hs : t ≫ r = s) :
    ((a ≫ q) ≫ h) ≫ s = (c ≫ p) ≫ r := by
  calc
    ((a ≫ q) ≫ h) ≫ s = ((a ≫ (q ≫ h)) ≫ t) ≫ r := by
      simp only [Category.assoc, hs]
    _ = (a ≫ ((q ≫ h) ≫ t)) ≫ r := by rw [Category.assoc a (q ≫ h) t]
    _ = (a ≫ (u ≫ p)) ≫ r := congrArg (fun k => (a ≫ k) ≫ r) hu.symm
    _ = ((a ≫ u) ≫ p) ≫ r := by rw [← Category.assoc a u p]
    _ = (c ≫ p) ≫ r := by rw [hb]

/-- Keep the chart's named composite until its equality is eliminated generically. -/
theorem compositeRankMap_from_namedChart
    {C : Type u} [Category.{v} C] {V M F J G B K : C}
    (a : V ⟶ M) (u : M ⟶ G) (c : V ⟶ G) (p : G ⟶ B)
    (q : M ⟶ F) (h : F ⟶ J) (t : J ⟶ B) (r : B ⟶ K) (s : J ⟶ K)
    (qh : M ⟶ J) (hqh : qh = q ≫ h)
    (hb : a ≫ u = c) (hu : u ≫ p = qh ≫ t) (hs : t ≫ r = s) :
    ((a ≫ q) ≫ h) ≫ s = (c ≫ p) ≫ r := by
  subst qh
  exact compositeRankMap_from_chart a u c p q h t r s hb hu hs

/-- Compatible cover maps give the same rank map on a refinement. -/
theorem compositeRankMap_from_coverTransition
    {C : Type u} [Category.{v} C] {V W M F J G B K : C}
    (e : V ⟶ W) (a : W ⟶ M) (q : M ⟶ F) (h : F ⟶ J) (s : J ⟶ K)
    (cv : V ⟶ G) (cw : W ⟶ G) (p : G ⟶ B) (r : B ⟶ K) (v : V ⟶ K)
    (hv : v = (cv ≫ p) ≫ r) (hw : ((a ≫ q) ≫ h) ≫ s = (cw ≫ p) ≫ r)
    (hc : e ≫ cw = cv) : v = (((e ≫ a) ≫ q) ≫ h) ≫ s := by
  calc
    v = (cv ≫ p) ≫ r := hv
    _ = ((e ≫ cw) ≫ p) ≫ r := congrArg (fun b => (b ≫ p) ≫ r) hc.symm
    _ = e ≫ (((a ≫ q) ≫ h) ≫ s) := by
      rw [hw]
      simp only [Category.assoc]
    _ = (((e ≫ a) ≫ q) ≫ h) ≫ s := by simp only [Category.assoc]

/-- Transport one chart rank equation along a cover transition. The original
arrows are inferred from the two equations. -/
theorem compositeRankMap_after_coverTransition
    {C : Type u} [Category.{v} C] {V W M F J G B K : C}
    {e : V ⟶ W} {a : W ⟶ M} {q : M ⟶ F} {h : F ⟶ J} {s : J ⟶ K}
    {cv : V ⟶ G} {cw : W ⟶ G} {p : G ⟶ B} {r : B ⟶ K}
    (hw : ((a ≫ q) ≫ h) ≫ s = (cw ≫ p) ≫ r)
    (hc : e ≫ cw = cv) : (((e ≫ a) ≫ q) ≫ h) ≫ s = (cv ≫ p) ≫ r :=
  (compositeRankMap_from_coverTransition e a q h s cv cw p r
    ((cv ≫ p) ≫ r) rfl hw hc).symm

/-- Compare two rank maps using their common original target. -/
theorem rankMaps_eq_of_same_target {α : Sort u} {a b c : α}
    (ha : a = c) (hb : b = c) : a = b :=
  ha.trans hb.symm

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedChartRankCompatibility
