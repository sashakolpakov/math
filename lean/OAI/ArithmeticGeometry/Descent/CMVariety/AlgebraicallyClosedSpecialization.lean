import OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization
import Mathlib.RingTheory.Localization.FractionRing

/-! # Algebraically Closed Specialization -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicallyClosedSpecialization.Abelian

noncomputable section

/-! A finite coefficient obstruction to points in any algebraically closed
ambient field, without requiring that field to be a fraction field. -/

open scoped TensorProduct

theorem finiteType_exists_algHom_to_closed_field
    (k Ω B : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [CommRing B] [Nontrivial B] [Algebra k B] [Algebra.FiniteType k B] :
    Nonempty (B →ₐ[k] Ω) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal B
  have : I.IsMaximal := hI
  let : Field (B ⧸ I) := Ideal.Quotient.field I
  have : Module.Finite k (B ⧸ I) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ I)
  let φ : (B ⧸ I) →ₐ[k] Ω := IsAlgClosed.lift
  exact ⟨φ.comp (Ideal.Quotient.mkₐ k I)⟩

theorem finiteType_no_closed_field_point_killed_by_nonzero
    (R Ω B : Type) [CommRing R] [IsDomain R] [Field Ω] [IsAlgClosed Ω]
    [Algebra R Ω] (hinj : Function.Injective (algebraMap R Ω))
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (h : IsEmpty (B →ₐ[R] Ω)) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R B r = 0 := by
  let K := FractionRing R
  let ι : K →+* Ω := IsFractionRing.lift (g := algebraMap R Ω) hinj
  let : Algebra K Ω := ι.toAlgebra
  have : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq
    (fun r => (IsFractionRing.lift_algebraMap hinj r).symm)
  let T := K ⊗[R] B
  have hT : Subsingleton T := by
    by_contra hT
    have : Nontrivial T := not_subsingleton_iff_nontrivial.mp hT
    obtain ⟨φ⟩ := finiteType_exists_algHom_to_closed_field K Ω T
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

end OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicallyClosedSpecialization.Abelian
