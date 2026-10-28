import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields

/-! # Curve Parameter -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter

noncomputable section

/-! A transcendental rational function on an integral curve makes its
function field a finite extension of the rational function field. All
scalar maps are the evaluation at that actual rational function. -/

variable (k L : Type) [Field k] [Field L] [Algebra k L]

abbrev polynomialAlgebra (g : L) : Algebra (Polynomial k) L := (Polynomial.aeval g).toRingHom.toAlgebra

theorem polynomialAlgebra_injective (g : L) (hg : Transcendental k g) :
    letI := polynomialAlgebra k L g
    Function.Injective (algebraMap (Polynomial k) L) := transcendental_iff_injective.mp hg

abbrev fractionAlgebra (g : L) (hg : Transcendental k g) : Algebra (FractionRing (Polynomial k)) L :=
  letI := polynomialAlgebra k L g
  letI : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (polynomialAlgebra_injective k L g hg)
  FractionRing.liftAlgebra (Polynomial k) L

theorem finite_parameter_extension [Algebra.EssFiniteType k L]
    (hdim : Algebra.trdeg k L = 1) (g : L) (hg : Transcendental k g) :
    letI := polynomialAlgebra k L g
    letI := fractionAlgebra k L g hg
    Module.Finite (FractionRing (Polynomial k)) L := by
  let := polynomialAlgebra k L g
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (polynomialAlgebra_injective k L g hg)
  let := fractionAlgebra k L g hg
  let : IsScalarTower k (Polynomial k) L := IsScalarTower.of_algHom (Polynomial.aeval g)
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  let : IsScalarTower k (FractionRing (Polynomial k)) L :=
    IsScalarTower.to₁₃₄ k (Polynomial k) (FractionRing (Polynomial k)) L
  let : Algebra.EssFiniteType k (FractionRing (Polynomial k)) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (FractionRing (Polynomial k))
  apply Cycles.Functoriality.FunctionFields.Construction.finite_of_equal_trdeg k (FractionRing (Polynomial k)) L
  rw [← Foundations.Scheme.TranscendenceDegreeTransfer.trdeg_eq_fractionRing k (Polynomial k), Polynomial.trdeg_of_isDomain, hdim]

theorem parameter_image (g : L) (hg : Transcendental k g) :
    letI := polynomialAlgebra k L g
    letI := fractionAlgebra k L g hg
    algebraMap (FractionRing (Polynomial k)) L
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) = g := by
  let := polynomialAlgebra k L g
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (polynomialAlgebra_injective k L g hg)
  let := fractionAlgebra k L g hg
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  rw [← IsScalarTower.algebraMap_apply]
  exact Polynomial.aeval_X g

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter
