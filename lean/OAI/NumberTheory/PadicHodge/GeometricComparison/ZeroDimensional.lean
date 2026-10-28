import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveConditional
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.Dimensional
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ThickeningCohomologyBound

/-! # Zero Dimensional -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The dimension-zero case of the original comparison target,
using genuine finite-scheme crystalline and étale cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.native_sharedPolynomial_of_dimension_zero (h0 : A.dimension = 0)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      let := hC
      ∃ P : Polynomial ℤ, A.IsWeilPolynomial ℓ P ∧
        A.crystallineFrobenius.charpoly = P.map (Int.castRingHom ℚ_[q]) := by
  have hdim : topologicalKrullDim A.specialFiber.scheme.left ≤ 0 := by
    simpa only [h0, Nat.cast_zero] using
      IntegralComparison.Smooth.ThickeningCohomologyBound.dimension_le A.specialFiber.scheme A.dimension
  obtain ⟨hsmall, het, P, _, hP, hEt⟩ := IntegralComparison.Zero.Dimensional.Comparison.comparison
    (ZMod q) A.specialFiber.scheme.hom q ℓ 1 (by simp) hdim A.specialFiber_projective 1
  let : FiniteDimensional (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q))
      (IntegralComparison.Interfaces.CrystallineCohomology q (ZMod q) A.specialFiber.scheme.hom 1) := hsmall
  let e : IntegralComparison.Interfaces.CrystallineCohomology q (ZMod q) A.specialFiber.scheme.hom 1
      ≃ₛₗ[(GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] A.Crystalline :=
    Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q A.specialFiber.scheme
  let T := IntegralComparison.Interfaces.crystallineQFrobenius q 1 (ZMod q) (by simp) A.specialFiber.scheme.hom 1
  have he : ∀ x, e (T x) = A.crystallineFrobenius (e x) :=
    Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv_frobenius q A.specialFiber.scheme
  let hC : FiniteDimensional ℚ_[q] A.Crystalline :=
    SemilinearCharpolyTo.SemilinearCharpoly.finite (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q) e
  refine ⟨hC, P, ⟨het, hEt⟩, ?_⟩
  rw [SemilinearCharpolyTo.SemilinearCharpoly.charpoly_map (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q) e T
    A.crystallineFrobenius he, hP, Polynomial.map_map]
  congr 1
  exact Subsingleton.elim _ _

end

theorem ZeroDimensional.comparison_and_weak_admissibility_of_dimension_zero
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq) (h0 : A.dimension = 0)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  obtain ⟨hC, W, hW, hCW⟩ := A.native_sharedPolynomial_of_dimension_zero h0 ℓ
  let : FiniteDimensional ℚ_[q] A.Crystalline := hC
  exact A.projective_comparisonTarget_of_shared_polynomial CompletionIntrinsic.nativeGeometricWeightInput
    κ jComplex ι hplace ρ P ℓ hℓq W hW hCW

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
