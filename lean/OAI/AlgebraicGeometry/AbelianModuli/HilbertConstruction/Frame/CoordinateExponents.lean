import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantBlockDegrees
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialFiniteSums

/-! # Coordinate Exponents -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateExponents

noncomputable section

/-! Each normalized point coordinate is a monomial in maximal minors.
All coordinates of that point have the same degree in every label block. -/
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {r m : ℕ}

theorem labeledDeterminantWeight_update_add (σ : Fin r → Fin m) (k : Fin r) (z i : Fin m) :
    DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k z) i + (if σ k = i then 1 else 0) =
      DeterminantBlockDegrees.labeledDeterminantWeight σ i + (if z = i then 1 else 0) := by
  have hnew := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
    (fun j => if Function.update σ k z j = i then 1 else 0) (Finset.mem_univ k)
  have hold := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
    (fun j => if σ j = i then 1 else 0) (Finset.mem_univ k)
  have he : (∑ j ∈ (Finset.univ : Finset (Fin r)).erase k,
      if Function.update σ k z j = i then 1 else 0) =
      ∑ j ∈ (Finset.univ : Finset (Fin r)).erase k, if σ j = i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, Function.update_self] at hnew
  unfold DeterminantBlockDegrees.labeledDeterminantWeight
  omega

theorem labeledDeterminantWeight_update_cross (σ : Fin r → Fin m) (k l : Fin r) (z e i : Fin m) :
    DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k z) i + DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ l e) i =
      DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ l z) i + DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k e) i := by
  have h₁ := labeledDeterminantWeight_update_add σ k z i
  have h₂ := labeledDeterminantWeight_update_add σ l e i
  have h₃ := labeledDeterminantWeight_update_add σ l z i
  have h₄ := labeledDeterminantWeight_update_add σ k e i
  omega

def frameCoordinateExponent (σ : Fin r → Fin m) (e z : Fin m) (k : Fin r) :
    (Fin r → Fin m) → ℕ :=
  Pi.single (Function.update σ k z) 1 +
    ∑ j ∈ (Finset.univ : Finset (Fin r)).erase k, Pi.single (Function.update σ j e) 1

theorem frameCoordinateExponent_degree (σ : Fin r → Fin m) (e z : Fin m) (k : Fin r) (i : Fin m) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (frameCoordinateExponent σ e z k) i =
      DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k z) i +
        ∑ j ∈ (Finset.univ : Finset (Fin r)).erase k, DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ j e) i := by
  have hsingle (j : Fin r → Fin m) :
      Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (Pi.single j 1) i = DeterminantBlockDegrees.labeledDeterminantWeight j i := by
    simp [Balanced.ExponentFiniteGeneration.monomialMultiDegree, Pi.single_apply]
  simp only [frameCoordinateExponent, Balanced.ExponentFiniteGeneration.monomialMultiDegree_add, MonomialFiniteSums.monomialMultiDegree_sum, hsingle]

theorem frameCoordinateExponent_degrees_equal (σ : Fin r → Fin m) (e z : Fin m) (k l : Fin r) (i : Fin m) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (frameCoordinateExponent σ e z k) i =
      Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (frameCoordinateExponent σ e z l) i := by
  rw [frameCoordinateExponent_degree, frameCoordinateExponent_degree]
  have hk := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
    (fun j => DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ j e) i) (Finset.mem_univ k)
  have hl := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
    (fun j => DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ j e) i) (Finset.mem_univ l)
  have hc := labeledDeterminantWeight_update_cross σ k l z e i
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateExponents
