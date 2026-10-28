import OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs

/-! # Parameter Scalars Tower -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterScalarsTower.BundleCycles.ParameterScalars

noncomputable section

/-! The zero-parameter local ring and its integral closure retain the
given ground-field scalars. The parameter is an actual integral element. -/

open OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage.BundleCycles.CurveParameter OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches

variable (k L : Type) [Field k] [Field L] [Algebra k L]
  (g : L) (hg : Transcendental k g)

theorem scalarTower :
    letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
    IsScalarTower k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localTower k L g hg
  let : IsScalarTower k (Polynomial k) L := IsScalarTower.of_algHom (Polynomial.aeval g)
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra_injective k L g hg)
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  let : IsScalarTower k (FractionRing (Polynomial k)) L :=
    IsScalarTower.to₁₃₄ k (Polynomial k) (FractionRing (Polynomial k)) L
  let : IsScalarTower k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) :=
    IsScalarTower.to₁₃₄ k (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k))
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)),
    ← IsScalarTower.algebraMap_apply]

abbrev closureScalarAlgebra :
    letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
    Algebra k (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) :=
  letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
  ((algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L)).comp
    (algebraMap k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k))).toAlgebra

theorem closureScalarTower :
    letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
    letI := closureScalarAlgebra k L g hg
    IsScalarTower k (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) L := by
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
  let := closureScalarAlgebra k L g hg
  let := scalarTower k L g hg
  let : IsScalarTower k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsScalarTower.to₁₃₄ k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) L

theorem parameter_integer :
    letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
    ∃ a : integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L, algebraMap (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) L a = g := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra k L g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localTower k L g hg
  refine ⟨algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L)
    (algebraMap (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) Polynomial.X), ?_⟩
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k))]
  exact CurveParameterImage.BundleCycles.CurveParameter.parameter_image k L g hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterScalarsTower.BundleCycles.ParameterScalars
