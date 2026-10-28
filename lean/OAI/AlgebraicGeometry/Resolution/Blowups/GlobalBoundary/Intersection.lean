import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntersectionCenters
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Intersection.Construction

noncomputable section

/-! A monomial schedule selects native global centers from labelled boundary ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def boundaryIntersectionSheaf {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) : X.IdealSheafData := C.sup D

theorem boundaryIntersectionSheaf_ideal {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (U : X.affineOpens) :
    (boundaryIntersectionSheaf D C).ideal U = C.sup (fun j => (D j).ideal U) := by
  classical
  induction C using Finset.induction_on with
  | empty => rfl
  | @insert j C hj ih =>
      simp only [boundaryIntersectionSheaf, Finset.sup_insert, Scheme.IdealSheafData.ideal_sup,
        Pi.sup_apply] at ih ⊢
      rw [ih]

theorem boundaryIntersectionSheaf_comap {X Y : Scheme.{u}} {ι : Type v}
    (D : ι → Y.IdealSheafData) (C : Finset ι) (f : X ⟶ Y) :
    (boundaryIntersectionSheaf D C).comap f = boundaryIntersectionSheaf (fun j => (D j).comap f) C := by
  classical
  induction C using Finset.induction_on with
  | empty => exact Scheme.IdealSheafData.comap_bot f
  | @insert j C hj ih =>
      simp only [boundaryIntersectionSheaf, Finset.sup_insert, Scheme.IdealSheafData.comap_sup] at ih ⊢
      rw [ih]

theorem boundaryIntersectionIdeal_eq_sup {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (C : Finset ι) :
    Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C = C.sup (fun j => Ideal.span {w j}) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (Finset.le_sup (f := fun l => Ideal.span {w l}) j.property)
      (Ideal.mem_span_singleton_self (w j.val))
  · apply Finset.sup_le
    intro j hj
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Boundary.Schedule.Construction.boundaryIntersection_mem w C j hj)

/-- Every equation chart sees the same global center, including its full ideal structure. -/
theorem boundaryIntersectionSheaf_local_equations {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hw : ∀ j ∈ C, (D j).ideal U = Ideal.span {w j}) :
    (boundaryIntersectionSheaf D C).ideal U = Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C := by
  rw [boundaryIntersectionSheaf_ideal, boundaryIntersectionIdeal_eq_sup]
  exact Finset.sup_congr rfl hw

/-- Different local equations for the same boundary ideal sheaves select the same center. -/
theorem boundaryIntersectionSheaf_equations_agree {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (U : X.affineOpens)
    (w z : ι → Γ(X, U)) (hw : ∀ j ∈ C, (D j).ideal U = Ideal.span {w j})
    (hz : ∀ j ∈ C, (D j).ideal U = Ideal.span {z j}) :
    Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C = Boundary.CountReduction.Construction.boundaryIntersectionIdeal z C :=
  (boundaryIntersectionSheaf_local_equations D C U w hw).symm.trans
    (boundaryIntersectionSheaf_local_equations D C U z hz)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Intersection.Construction
