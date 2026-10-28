import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondClasses
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalHorizontalBoundary
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainBoundary

/-! # Total Second Elimination -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondElimination

noncomputable section

/-! An actual horizontal boundary in row homology can be removed from a filtered total cycle. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondClasses

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem normalize (q p : ℕ) (x : TotalFiltration.cycles K (q + p + 1) (q + 1))
    (y : CochainClasses.cycles (K.X q) p)
    (hy : HomologicalComplex.homologyMap (K.d q (q + 1)) p
      (CochainClasses.classMap (K.X q) p y) =
        TotalFiltration.rowClassMap K (q + p + 1) (q + 1) p (by omega) x) :
    ∃ x' : TotalFiltration.cycles K (q + p + 1) (q + 1),
      TotalFiltration.classMap K (q + p + 1) (q + 1) x' = TotalFiltration.classMap K (q + p + 1) (q + 1) x ∧
      TotalFiltration.rowClassMap K (q + p + 1) (q + 1) p (by omega) x' = 0 := by
  let z := K.ιTotal (.up ℕ) q p (q + p) rfl y.val
  let x₀ := CochainBoundary.subBoundary (K.total (.up ℕ)) (q + p) x.val z
  have hb : TotalCoordinates.ZeroRowsBefore K (q + p + 1) x₀.val (q + 1) := by
    intro a b hab ha
    change (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      (x.val.val - (K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y.val)) = 0
    rw [map_sub, TotalHorizontalBoundary.before_next_row K q p a b ha y.val y.property, sub_zero]
    exact x.property a b hab ha
  let x' : TotalFiltration.cycles K (q + p + 1) (q + 1) := ⟨x₀, hb⟩
  refine ⟨x', CochainBoundary.class_eq (K.total (.up ℕ)) (q + p) x.val z, ?_⟩
  have hr : TotalFiltration.rowCycleMap K (q + p + 1) (q + 1) p (by omega) x' =
      TotalFiltration.rowCycleMap K (q + p + 1) (q + 1) p (by omega) x -
        CochainClassNaturality.cycleMap (K.d q (q + 1)) p y := by
    apply Subtype.ext
    change (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1)
      (x.val.val - (K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y.val)) =
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1) x.val.val - (K.d q (q + 1)).f p y.val
    rw [map_sub, TotalHorizontalBoundary.next_row]
  change CochainClasses.classMap (K.X (q + 1)) p
    (TotalFiltration.rowCycleMap K (q + p + 1) (q + 1) p (by omega) x') = 0
  rw [hr, map_sub, CochainClassNaturality.naturality_apply, hy]
  exact sub_self _

theorem zero_class_lifts (n q p : ℕ) (hdeg : q + p = n) (x : TotalFiltration.cycles K n q)
    (hx : TotalSecondClasses.secondClassMap K n q p hdeg x = 0) :
    ∃ y : TotalFiltration.cycles K n (q + 1), TotalFiltration.classMap K n (q + 1) y = TotalFiltration.classMap K n q x := by
  cases q with
  | zero =>
      have h := (CochainClasses.classMap_zero_eq_zero_iff (TotalSecondClasses.horizontal K p)
        (TotalSecondClasses.secondCycleMap K n 0 p hdeg x)).mp hx
      exact TotalFiltration.zero_row_class_lifts K n 0 p hdeg x (congrArg Subtype.val h)
  | succ q =>
      have hn : n = q + p + 1 := by omega
      cases hn
      obtain ⟨η, hη⟩ := (CochainClasses.classMap_succ_eq_zero_iff (TotalSecondClasses.horizontal K p) q
        (TotalSecondClasses.secondCycleMap K (q + p + 1) (q + 1) p hdeg x)).mp hx
      obtain ⟨y, hy⟩ := CochainClasses.classMap_surjective (K.X q) p η
      have hstep : HomologicalComplex.homologyMap (K.d q (q + 1)) p
          (CochainClasses.classMap (K.X q) p y) =
        TotalFiltration.rowClassMap K (q + p + 1) (q + 1) p (by omega) x := by
        rw [hy]
        exact hη
      obtain ⟨x', hclass, hrow⟩ := normalize K q p x y hstep
      obtain ⟨y', hy'⟩ := TotalFiltration.zero_row_class_lifts K (q + p + 1) (q + 1) p (by omega) x' hrow
      exact ⟨y', hy'.trans hclass⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondElimination
