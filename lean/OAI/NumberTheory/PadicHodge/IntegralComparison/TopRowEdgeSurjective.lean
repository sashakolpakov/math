import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration

/-! # Top Row Edge Surjective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeSurjective

noncomputable section

/-! If rows above the final row vanish and earlier rows have no
cohomology on the relevant diagonal, the native final-row edge map
surjects onto total cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)] (c : ℕ)
  (hc : ∀ q, (K.d c (c + 1)).f q = 0)
  (hbound : ∀ a b, c < a → Subsingleton ((K.X a).X b))

include hbound in
theorem cycleMap_rowCycleMap (n : ℕ)
    (x : Module.TotalFiltration.cycles K (c + n) c) :
    TopRowEdge.cycleMap K c hc n (Module.TotalFiltration.rowCycleMap K (c + n) c n rfl x) = x.val := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Module.TotalCoordinates.eq_zero_of_coordinates K (c + n)
  intro i
  rw [map_sub]
  change (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (c + n - i) (c + n)
      (K.ιTotal (.up ℕ) c n (c + n) rfl ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) c n (c + n) x.val.val)) -
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (c + n - i) (c + n) x.val.val = 0
  by_cases hi : c = (i : ℕ)
  · rw [← hi, Nat.add_sub_cancel_left, Module.TotalInjectionElements.projection_same, sub_self]
  · rw [Module.TotalInjectionElements.projection_other K c n (c + n) rfl
      i (c + n - i) hi]
    by_cases hilow : (i : ℕ) < c
    · rw [x.property i (c + n - i) (by omega) hilow, sub_self]
    · let := hbound i (c + n - i) (by omega)
      exact Subsingleton.elim _ _

include hbound in
theorem map_rowClassMap (n : ℕ)
    (x : Module.TotalFiltration.cycles K (c + n) c) :
    TopRowEdge.map K c hc n (Module.TotalFiltration.rowClassMap K (c + n) c n rfl x) =
      Module.TotalFiltration.classMap K (c + n) c x :=
  (TopRowEdge.map_class K c hc n _).trans
    (congrArg (Module.CochainClasses.classMap (K.total (.up ℕ)) (c + n))
      (cycleMap_rowCycleMap K c hc hbound n x))

include hbound in
theorem surjective (n : ℕ)
    (hrows : ∀ q, q < c → Subsingleton ((K.X q).homology (c + n - q))) :
    Function.Surjective (TopRowEdge.map K c hc n) := by
  intro ξ
  have lift : ∀ q, q ≤ c → ∃ x : Module.TotalFiltration.cycles K (c + n) q,
      Module.TotalFiltration.classMap K (c + n) q x = ξ := by
    intro q
    induction q with
    | zero =>
        intro _
        obtain ⟨x, hx⟩ := Module.CochainClasses.classMap_surjective (K.total (.up ℕ)) (c + n) ξ
        exact ⟨⟨x, by intro a b hab ha; omega⟩, hx⟩
    | succ q ih =>
        intro hq
        obtain ⟨x, hx⟩ := ih (by omega)
        let := hrows q (by omega)
        obtain ⟨y, hy⟩ := Module.TotalFiltration.zero_row_class_lifts K (c + n) q
          (c + n - q) (by omega) x (Subsingleton.elim _ _)
        exact ⟨y, hy.trans hx⟩
  obtain ⟨x, hx⟩ := lift c le_rfl
  exact ⟨Module.TotalFiltration.rowClassMap K (c + n) c n rfl x,
    (map_rowClassMap K c hc hbound n x).trans hx⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeSurjective
