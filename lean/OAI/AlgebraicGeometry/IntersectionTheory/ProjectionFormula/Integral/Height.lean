import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Ideal.Height
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension

/-! # Height -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Height

noncomputable section

/-! An integral domain extension of a finite-type domain over a field
preserves prime heights. Noether normalization supplies a common normal
polynomial base; going down computes both heights over that base. -/

theorem integral_height_under (k R S : Type*) [Field k] [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra k R] [Algebra.FiniteType k R]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    (q.asIdeal.under R).height = q.asIdeal.height := by
  obtain ⟨n, f, hf, hint⟩ := exists_integral_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P R := ⟨hint⟩
  let : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hf
  let : Algebra P S := ((algebraMap R S).comp f.toRingHom).toAlgebra
  let : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsIntegral P S := Algebra.IsIntegral.trans R
  let : IsIntegrallyClosed P := inferInstance
  let : FaithfulSMul P S :=
    (faithfulSMul_iff_algebraMap_injective P S).mpr (hinj.comp hf)
  have hR := DivisorClass.Chern.IntegralDimension.Construction.integral_comap_height (R := P) (S := R)
    (⟨q.asIdeal.under R, inferInstance⟩ : PrimeSpectrum R)
  have hS := DivisorClass.Chern.IntegralDimension.Construction.integral_comap_height (R := P) (S := S) q
  rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at hR hS
  exact hR.trans hS.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Height
