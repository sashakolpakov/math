import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.CrystallinePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.GenericFiberNaturality

/-! # Naturality Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Transfer a proved integral naturality identity to the actual
rational crystalline/de Rham comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance Geometry.AbelianH1Model.naturality_criterion_integral_separated : A.integral.scheme.left.IsSeparated := ⟨by
  rw [← terminal.comp_from A.integral.scheme.hom]
  infer_instance⟩

theorem Geometry.AbelianH1Model.integralReductionEndomorphism_square (f : A.ExtendingEndomorphism) :
    A.integralReductionMorphism ≫ f.integral.toMul.hom.hom.left =
      (A.specialEndomorphism f).left ≫ A.integralReductionMorphism :=
  (pullback.lift_fst _ _ _).symm

theorem Geometry.AbelianH1Model.transportedIntegralCrystallinePullback_eq_of_naturality (f : A.ExtendingEndomorphism)
    (hn : ∀ x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1,
      A.constructedIntegralCrystallineEquiv (A.integralDeRhamPullback f x) =
        IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q (A.specialEndomorphism f)
          (A.constructedIntegralCrystallineEquiv x)) :
    A.transportedIntegralCrystallinePullback (A.specialEndomorphism f) = A.integralDeRhamPullback f := by
  apply LinearMap.ext
  intro x
  apply A.constructedIntegralCrystallineEquiv.injective
  exact (A.transportedIntegralCrystallinePullback_equiv (A.specialEndomorphism f) x).trans
    (hn x).symm

theorem Geometry.AbelianH1Model.constructedRationalCrystallineEquiv_naturality_of_integral (f : A.ExtendingEndomorphism)
    (hn : ∀ x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1,
      A.constructedIntegralCrystallineEquiv (A.integralDeRhamPullback f x) =
        IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q (A.specialEndomorphism f)
          (A.constructedIntegralCrystallineEquiv x))
    (x : ℚ_[q] ⊗[ℤ_[q]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.constructedRationalCrystallineEquiv ((A.integralDeRhamPullback f).baseChange ℚ_[q] x) =
      A.crystallinePullback f (A.constructedRationalCrystallineEquiv x) := by
  have h := A.constructedRationalCrystallineEquiv_pullback (A.specialEndomorphism f)
  rw [A.transportedIntegralCrystallinePullback_eq_of_naturality f hn] at h
  exact LinearMap.congr_fun h x

theorem Geometry.AbelianH1Model.constructedCrystallineDeRhamEquiv_naturality_of_integral (f : A.ExtendingEndomorphism)
    (hn : ∀ x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1,
      A.constructedIntegralCrystallineEquiv (A.integralDeRhamPullback f x) =
        IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q (A.specialEndomorphism f)
          (A.constructedIntegralCrystallineEquiv x)) (x : A.Crystalline) :
    A.constructedCrystallineDeRhamEquiv (A.crystallinePullback f x) =
      A.deRhamPullback f (A.constructedCrystallineDeRhamEquiv x) := by
  obtain ⟨y, rfl⟩ := A.constructedRationalCrystallineEquiv.surjective x
  change A.integral_generic_deRham_hone
    (A.constructedRationalCrystallineEquiv.symm
      (A.crystallinePullback f (A.constructedRationalCrystallineEquiv y))) =
    A.deRhamPullback f
      (A.integral_generic_deRham_hone
        (A.constructedRationalCrystallineEquiv.symm (A.constructedRationalCrystallineEquiv y)))
  rw [← A.constructedRationalCrystallineEquiv_naturality_of_integral f hn,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact A.integral_generic_deRham_hone_naturality f y

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
