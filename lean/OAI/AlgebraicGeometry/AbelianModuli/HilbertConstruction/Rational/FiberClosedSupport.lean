import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Fiber Closed Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberClosedSupport

noncomputable section

/-! Finiteness of rational scheme fibers detects finite set-theoretic fibers at closed points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

theorem closedFiber_finite_of_rationalFibers (f : X ⟶ Y) (p : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType p]
    (h : ∀ (a : Spec (.of K) ⟶ Y), a ≫ p = 𝟙 _ → IsFinite (Limits.pullback.snd f a))
    (y : Y) (hy : IsClosed ({y} : Set Y)) : (f ⁻¹' {y}).Finite := by
  let a := pointOfClosedPoint p y hy
  have : IsFinite (Limits.pullback.snd f a) := h a (pointOfClosedPoint_comp p y hy)
  have hP : Finite (Limits.pullback f a : Scheme.{u}) := by
    apply Finite.of_finite_univ
    simpa only [Set.preimage_univ] using
      (Limits.pullback.snd f a).finite_preimage (Set.finite_univ : (Set.univ : Set (Spec (.of K))).Finite)
  have hR : (Set.range (Limits.pullback.fst f a)).Finite := Set.finite_range _
  apply hR.subset
  intro z hz
  change f z = y at hz
  let k : Spec (.of K) := Classical.choice inferInstance
  have he : f z = a k := hz.trans (pointOfClosedPoint_apply p y hy k).symm
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback z k he
  exact ⟨w, hw⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberClosedSupport
