import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Closed Points -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ClosedPoints

noncomputable section

/-! # Algebraic closed points avoiding a nonzero function

This is a supporting algebraic lemma for preserving the original integral-group
scope when constructing its geometric endomorphism algebra.
-/

variable {K A : Type*} [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]

/-- A nonzero regular function on a finite-type integral algebra over an algebraically
closed field is nonzero at some actual rational point. -/
theorem exists_algHom_ne_zero (c : A) (hc : c ≠ 0) :
    ∃ f : A →ₐ[K] K, f c ≠ 0 := by
  let S := Localization.Away c
  let : IsDomain S := Localization.Away.isDomain hc
  let : Algebra.FiniteType K S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K A) (inferInstance : Algebra.FiniteType A S)
  obtain ⟨I, hI⟩ := Ideal.exists_maximal S
  let := hI
  let : Field (S ⧸ I) := Ideal.Quotient.field I
  let : Module.Finite K (S ⧸ I) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ I)
  let q : S →ₐ[K] K := (IsAlgClosed.lift : (S ⧸ I) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K I)
  let f : A →ₐ[K] K := q.comp (IsScalarTower.toAlgHom K A S)
  refine ⟨f, ?_⟩
  exact ((IsLocalization.Away.algebraMap_isUnit c (S := S)).map q.toRingHom).ne_zero

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ClosedPoints
