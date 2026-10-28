import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary

/-! # Total Component Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentLift

noncomputable section

/-! Actual maps into a first-quadrant total are finite sums of their
bidegree components. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]
  {A : C} (n : ℕ)

def lift (f : ∀ p q, p + q = n → (A ⟶ (K.X p).X q)) : A ⟶ (K.total (.up ℕ)).X n :=
  ∑ i : Fin (n + 1), f i (n - i) (by omega) ≫
    K.ιTotal (.up ℕ) i (n - i) n (by change (i : ℕ) + (n - i) = n; omega)

@[reassoc]
theorem lift_projection (f : ∀ p q, p + q = n → (A ⟶ (K.X p).X q))
    (p q : ℕ) (h : p + q = n) :
    lift K n f ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n = f p q h := by
  classical
  unfold lift
  rw [sum_comp]
  let j : Fin (n + 1) := ⟨p, by omega⟩
  rw [Finset.sum_eq_single j]
  · have hq : n - p = q := by omega
    subst q
    simp [j]
  · intro i _ hij
    have hip : (i : ℕ) ≠ p := by
      intro h
      apply hij
      exact Fin.ext h
    simp [hip]
  · simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentLift
