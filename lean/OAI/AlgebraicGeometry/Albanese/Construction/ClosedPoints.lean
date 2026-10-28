import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Closed Points -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A rational point in the set-theoretic image of a finite-type morphism over
an algebraically closed field lifts to a rational point of its source. -/
theorem pointMap_range_iff {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (q : Over.mk (𝟙 (Spec (.of K))) ⟶ Y) :
    (∃ p : Over.mk (𝟙 (Spec (.of K))) ⟶ X, p ≫ f = q) ↔
      q.left (IsLocalRing.closedPoint K) ∈ Set.range f.left := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.left (IsLocalRing.closedPoint K), rfl⟩
  · intro hq
    have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
    have hclosed : IsClosed {q.left (IsLocalRing.closedPoint K)} :=
      ((pointEquivClosedPoint Y.hom) ⟨q.left, q.w⟩).property
    have hfiber : (f.left ⁻¹' {q.left (IsLocalRing.closedPoint K)}).Nonempty := by
      obtain ⟨x, hx⟩ := hq
      exact ⟨x, hx⟩
    obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints hfiber
      ((hclosed.preimage f.left.continuous).isLocallyClosed)
    change IsClosed {x} at hxclosed
    let p : Over.mk (𝟙 (Spec (.of K))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hxclosed)
        (pointOfClosedPoint_comp X.hom x hxclosed)
    refine ⟨p, ?_⟩
    ext1
    apply ext_of_apply_closedPoint_eq Y.hom
    · simp
    · exact q.w
    · change f.left (pointOfClosedPoint X.hom x hxclosed (IsLocalRing.closedPoint K)) = _
      exact (congrArg f.left
        (pointOfClosedPoint_apply X.hom x hxclosed (IsLocalRing.closedPoint K))).trans hx

/-- Rational points detect morphisms from a reduced finite-type scheme to a
separated finite-type scheme over an algebraically closed field. -/
theorem hom_ext_of_points {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (.of K)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ p : Over.mk (𝟙 (Spec (.of K))) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  ext1
  apply ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Over.mk (𝟙 (Spec (.of K))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have hp : p.left (IsLocalRing.closedPoint K) = x :=
      pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint K)
    calc
      f.left x = f.left (p.left (IsLocalRing.closedPoint K)) := congrArg f.left hp.symm
      _ = g.left (p.left (IsLocalRing.closedPoint K)) :=
        congrArg (fun q : Over.mk (𝟙 (Spec (.of K))) ⟶ Y =>
          q.left (IsLocalRing.closedPoint K)) (h p)
      _ = g.left x := congrArg g.left hp
  · exact f.w.trans g.w.symm

end

end OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
