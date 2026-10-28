import Mathlib.Topology.Instances.Complex
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Topology.NhdsWithin

/-! # Dense Algebraic Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.DenseAlgebraicCoordinates.Abelian

noncomputable section

/-! Algebraic complex coordinates are dense. This supplies the coordinate
approximation step for choosing arithmetic fibers in native neighborhoods. -/

open Set _root_.Complex
open scoped _root_.Topology

theorem complex_subfield_dense_of_I_mem (K : Subfield ℂ) (hI : Complex.I ∈ K) :
    Dense (K : Set ℂ) := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K) with hreal | htop
  · have hi := K.le_topologicalClosure hI
    rw [hreal] at hi
    obtain ⟨r, hr⟩ := hi
    have h := congrArg Complex.im hr
    simp at h
  · apply dense_iff_closure_eq.mpr
    change (K.topologicalClosure : Set ℂ) = Set.univ
    rw [htop]
    rfl

theorem algebraic_complex_coordinates_dense : Dense {z : ℂ | IsAlgebraic ℚ z} := by
  let K := (algebraicClosure ℚ ℂ).toSubfield
  have hi : IsAlgebraic ℚ Complex.I := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [Complex.I_sq]
    exact (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ)).neg
  have hiK : Complex.I ∈ K := mem_algebraicClosure_iff.mpr hi
  have hK : (K : Set ℂ) = {z : ℂ | IsAlgebraic ℚ z} := by
    ext z
    exact mem_algebraicClosure_iff
  rw [← hK]
  exact complex_subfield_dense_of_I_mem K hiK

theorem algebraic_coordinate_tuples_dense (Index : Type*) :
    Dense {z : Index → ℂ | ∀ i, IsAlgebraic ℚ (z i)} := by
  simpa only [Set.pi, Set.mem_univ, forall_true_left, Set.mem_ofPred_eq] using
    dense_pi (s := fun _ : Index => {z : ℂ | IsAlgebraic ℚ z}) Set.univ
      (fun _ _ => algebraic_complex_coordinates_dense)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.DenseAlgebraicCoordinates.Abelian
