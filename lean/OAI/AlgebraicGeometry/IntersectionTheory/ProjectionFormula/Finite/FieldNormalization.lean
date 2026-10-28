import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Normalization
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Field Normalization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.FieldNormalization

noncomputable section

/-! The integral closure of a finite-type characteristic-zero domain in a
finite extension of its function field is finite. This supplies the finite
intermediate scheme for a general proper generically finite morphism. -/

theorem finite_over_normal_base
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    [Field K] [Field L] [Algebra A B] [Module.Finite A B]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Module.Finite K L]
    [Algebra A L] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hi : Function.Injective (algebraMap A L)) :
    Module.Finite B (integralClosure B L) := by
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hi
  let : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let : IsIntegralClosure (integralClosure B L) A L :=
    ⟨IsIntegralClosure.algebraMap_injective (integralClosure B L) B L,
      fun {x} => ⟨fun hx =>
        (IsIntegralClosure.isIntegral_iff (A := integralClosure B L) (R := B)).mp
          (show IsIntegral B x from hx.tower_top),
        fun hx => isIntegral_trans (R := A) x
          ((IsIntegralClosure.isIntegral_iff (A := integralClosure B L) (R := B)).mpr hx)⟩⟩
  let : Module.Finite A (integralClosure B L) :=
    IsIntegralClosure.finite A K L (integralClosure B L)
  exact Module.Finite.of_restrictScalars_finite A B (integralClosure B L)

theorem finite_integralClosure_extension
    (k B K L : Type*) [Field k] [CharZero k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] [Field K] [Field L]
    [Algebra B K] [IsFractionRing B K] [Algebra K L] [Module.Finite K L]
    [Algebra B L] [IsScalarTower B K L] :
    Module.Finite B (integralClosure B L) := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k B
  let A := MvPolynomial (Fin n) k
  let : Algebra A B := g.toRingHom.toAlgebra
  let : Module.Finite A B := hfinite
  let : Algebra A K := ((algebraMap B K).comp g.toRingHom).toAlgebra
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap K L (algebraMap B K (g a)) = algebraMap B L (g a)
    exact (IsScalarTower.algebraMap_apply B K L (g a)).symm)
  have hiK : Function.Injective (algebraMap A K) := (IsFractionRing.injective B K).comp hg
  have hiL : Function.Injective (algebraMap A L) := (algebraMap K L).injective.comp hiK
  let : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hiK
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hiL
  let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  let : IsScalarTower (FractionRing A) K L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  let : Module.Finite (FractionRing A) K :=
    Normalization.finite_fraction_extension A B (FractionRing A) K hiK
  let : Module.Finite (FractionRing A) L := Module.Finite.trans K L
  exact finite_over_normal_base A B (FractionRing A) L hiL

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.FieldNormalization
