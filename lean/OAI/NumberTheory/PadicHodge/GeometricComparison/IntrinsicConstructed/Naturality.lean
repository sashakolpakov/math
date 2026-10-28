import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.NaturalityCriterion

/-! # Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Naturality.AbelianModel

noncomputable section

/-! Naturality of the actual constructed crystalline/de Rham comparison
for every extending endomorphism of the original abelian model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructed_naturality_integral_separated : A.integral.scheme.left.IsSeparated := ⟨by
  rw [← terminal.comp_from A.integral.scheme.hom]
  infer_instance⟩

local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := q)
  (J := Ideal.span {(q : WittVector q (ZMod q))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
  (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedIntegralCrystallineEquiv_naturality (f : A.ExtendingEndomorphism)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.constructedIntegralCrystallineEquiv (A.integralDeRhamPullback f x) =
      IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q (A.specialEndomorphism f)
        (A.constructedIntegralCrystallineEquiv x) :=
  (IntrinsicPadic.IntegralNaturality.IntrinsicPadicIntegralGeometricNaturality.naturality q A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare I A.specialFiber_projective
    f.integral.toMul.hom.hom (A.specialEndomorphism f) (A.integralReductionEndomorphism_square f) x).symm

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.transportedIntegralCrystallinePullback_eq (f : A.ExtendingEndomorphism) :
    A.transportedIntegralCrystallinePullback (A.specialEndomorphism f) = A.integralDeRhamPullback f :=
  A.transportedIntegralCrystallinePullback_eq_of_naturality f
    (A.constructedIntegralCrystallineEquiv_naturality f)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedRationalCrystallineEquiv_naturality (f : A.ExtendingEndomorphism)
    (x : ℚ_[q] ⊗[ℤ_[q]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.constructedRationalCrystallineEquiv ((A.integralDeRhamPullback f).baseChange ℚ_[q] x) =
      A.crystallinePullback f (A.constructedRationalCrystallineEquiv x) :=
  A.constructedRationalCrystallineEquiv_naturality_of_integral f
    (A.constructedIntegralCrystallineEquiv_naturality f) x

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedCrystallineDeRhamEquiv_naturality (f : A.ExtendingEndomorphism) (x : A.Crystalline) :
    A.constructedCrystallineDeRhamEquiv (A.crystallinePullback f x) =
      A.deRhamPullback f (A.constructedCrystallineDeRhamEquiv x) :=
  A.constructedCrystallineDeRhamEquiv_naturality_of_integral f
    (A.constructedIntegralCrystallineEquiv_naturality f) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Naturality.AbelianModel
