import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Algebraic Specialization -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization.Construction

noncomputable section

/-! Algebraic specialization and a finite-denominator obstruction to points.
The specialization construction adapts the independent algebraic argument in
AlgebraicSpecialization. The final lemma is used for bounded polynomial
factorization parameter spaces in the geometric-component argument. -/

open scoped TensorProduct

universe u

theorem finiteType_exists_algHom_to_algClosure
    (k B : Type u) [Field k] [CommRing B] [Nontrivial B] [Algebra k B]
    [Algebra.FiniteType k B] : Nonempty (B →ₐ[k] AlgebraicClosure k) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal B
  let : I.IsMaximal := hI
  let : Field (B ⧸ I) := Ideal.Quotient.field I
  let : Module.Finite k (B ⧸ I) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ I)
  let φ : (B ⧸ I) →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  exact ⟨φ.comp (Ideal.Quotient.mkₐ k I)⟩

theorem finiteType_specialization_nonzero
    (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] {b : B} (hb : b ≠ 0) :
    ∃ φ : B →ₐ[k] AlgebraicClosure k, φ b ≠ 0 := by
  let C := Localization.Away b
  have hinj : Function.Injective (algebraMap B C) :=
    IsLocalization.injective C (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  let : Nontrivial C := nontrivial_of_ne (algebraMap B C 0) (algebraMap B C 1)
    (fun h ↦ zero_ne_one (hinj h))
  obtain ⟨ψ⟩ := finiteType_exists_algHom_to_algClosure k C
  let φ : B →ₐ[k] AlgebraicClosure k := ψ.comp (IsScalarTower.toAlgHom k B C)
  refine ⟨φ, ?_⟩
  have hbunit : IsUnit (algebraMap B C b) := IsLocalization.Away.algebraMap_isUnit b
  exact (hbunit.map ψ.toRingHom).ne_zero

theorem finiteType_no_geometric_generic_point_killed_by_nonzero
    (R K B : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (h : IsEmpty (B →ₐ[R] AlgebraicClosure K)) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R B r = 0 := by
  let T := K ⊗[R] B
  have hT : Subsingleton T := by
    by_contra hT
    have : Nontrivial T := not_subsingleton_iff_nontrivial.mp hT
    obtain ⟨φ⟩ := finiteType_exists_algHom_to_algClosure K T
    exact h.false ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) T :=
    IsLocalization.tensorRight (R := R) (S := B) K (nonZeroDivisors R)
  have hz : (0 : B) ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors R) :=
    (IsLocalization.subsingleton_iff
      (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (S := T)).mp hT
  obtain ⟨r, hr, he⟩ := hz
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, he⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization.Construction
