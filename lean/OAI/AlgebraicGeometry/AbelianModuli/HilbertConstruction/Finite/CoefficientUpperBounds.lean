import Mathlib.RingTheory.FiniteType

/-! # Coefficient Upper Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientUpperBounds

noncomputable section

/-! Finitely many finite coefficient algebras fit inside one finite coefficient algebra. -/

universe u v w

theorem exists_finiteType_coefficient_upperBound
    {B : Type u} [CommRing B] {R : Type v} [CommRing R] [Algebra B R]
    {ι : Type w} [Finite ι] (C : ι → Subalgebra B R) (hC : ∀ i, (C i).FG) :
    ∃ D : Subalgebra B R, D.FG ∧ ∀ i, C i ≤ D := by
  classical
  let := Fintype.ofFinite ι
  have hfg (s : Finset ι) : (s.sup C).FG := by
    induction s using Finset.induction_on with
    | empty => exact Subalgebra.fg_bot
    | @insert i s hi hs =>
      rw [Finset.sup_insert]
      exact (hC i).sup hs
  exact ⟨Finset.univ.sup C, hfg _, fun i => Finset.le_sup (Finset.mem_univ i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientUpperBounds
