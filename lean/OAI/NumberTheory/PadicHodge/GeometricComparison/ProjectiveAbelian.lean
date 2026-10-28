import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ProjectiveComplexNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianComparisonNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension

/-! # Projective Abelian -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The given projective presentation supplies the actual filtered,
endomorphism-natural complex comparison without an BettiComparison assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

def Geometry.AbelianH1Model.projectiveNativeComplexComparison :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 ≃ₗ[ℂ] A.ComplexBetti j :=
  Intrinsic.ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv (A.complexFiber j).scheme P 1

theorem Geometry.AbelianH1Model.projectiveNativeComplexComparison_filtration (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r).map
        (A.projectiveNativeComplexComparison j P).toLinearMap = A.bettiFiltration j P r :=
  (Intrinsic.ProjectiveComplex.ProjectiveComplexComparison.nativeEquiv_filtration (A.complexFiber j).scheme P 1 r).trans
    (Betti.ComplexComparison.projectiveFiltration_one (A.smoothProjectiveFiber j P) r)

theorem Geometry.AbelianH1Model.projectiveAlgebraicBettiComparison_exists :
    ∃ cmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j,
      (∀ f : A.ExtendingEndomorphism, ∀ x,
        cmp (A.complexAlgebraicPullback j f x) = A.complexBettiPullback j f (cmp x)) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration j i).map cmp.toLinearMap = A.bettiFiltration j P i) := by
  let : Algebra K ℂ := j.toAlgebra
  let e : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ]
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 :=
    A.complexAlgebraicComparison j
  let d : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 ≃ₗ[ℂ]
      A.ComplexBetti j := A.projectiveNativeComplexComparison j P
  have hd (f : A.ExtendingEndomorphism) :
      d.toLinearMap.comp (GeometricComparison.DeRham.Int.pullback (A.complexEndomorphism j f) 1) =
      (A.complexBettiPullback j f).comp d.toLinearMap :=
    Intrinsic.ProjectiveComplexNaturality.ProjectiveComplexComparison.nativeEquiv_naturality P P (A.complexEndomorphism j f) 1
  have hP (i : ℤ) : (A.complexAlgebraicFiltration j i).map e.toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 i :=
    A.complexAlgebraicComparison_filtration j i
  have hQ (i : ℤ) : (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 i).map
      d.toLinearMap = A.bettiFiltration j P i := A.projectiveNativeComplexComparison_filtration j P i
  exact Geometry.AbelianH1Model.comparison_trans_exists (F := ℂ) (M := A.ComplexAlgebraicDeRham j)
    (N := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1) (T := A.ComplexBetti j)
    (I := A.ExtendingEndomorphism) (J := ℤ) e d (A.complexAlgebraicPullback j)
    (fun f => GeometricComparison.DeRham.Int.pullback (A.complexEndomorphism j f) 1) (A.complexBettiPullback j)
    (A.complexAlgebraicFiltration j) (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1)
    (A.bettiFiltration j P) (A.complexAlgebraicComparison_naturality j) hd hP hQ

def Geometry.AbelianH1Model.projectiveAlgebraicBettiComparison :
    A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j :=
  (A.projectiveAlgebraicBettiComparison_exists j P).choose

theorem Geometry.AbelianH1Model.projectiveAlgebraicBettiComparison_naturality
    (f : A.ExtendingEndomorphism) (x : A.ComplexAlgebraicDeRham j) :
    A.projectiveAlgebraicBettiComparison j P (A.complexAlgebraicPullback j f x) =
      A.complexBettiPullback j f (A.projectiveAlgebraicBettiComparison j P x) :=
  (A.projectiveAlgebraicBettiComparison_exists j P).choose_spec.1 f x

theorem Geometry.AbelianH1Model.projectiveAlgebraicBettiComparison_filtration (r : ℤ) :
    (A.complexAlgebraicFiltration j r).map
        (A.projectiveAlgebraicBettiComparison j P).toLinearMap = A.bettiFiltration j P r :=
  (A.projectiveAlgebraicBettiComparison_exists j P).choose_spec.2 r

include j P in
theorem Geometry.AbelianH1Model.algebraicDeRham_finite_of_projective_comparison :
    FiniteDimensional K A.AlgebraicDeRham := by
  let : Algebra K ℂ := j.toAlgebra
  let : FiniteDimensional ℂ (A.ComplexBetti j) := A.complexBetti_finiteDimensional j P
  exact Finite.FiniteScalarExtension.ScalarExtension.finite_of_comparison K ℂ A.AlgebraicDeRham
    (A.projectiveAlgebraicBettiComparison j P)

include j P in
theorem Geometry.AbelianH1Model.localDeRham_finite_of_projective_comparison :
    FiniteDimensional ℚ_[q] A.DeRham := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham :=
    A.algebraicDeRham_finite_of_projective_comparison j P
  exact A.localAlgebraicComparison.finiteDimensional

theorem Geometry.AbelianH1Model.projective_algebraic_filtered_comparisons :
    ∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
      (bettiCmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j),
      (∀ f : A.ExtendingEndomorphism,
        (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
        (∀ x, bettiCmp (A.complexAlgebraicPullback j f x) =
          A.complexBettiPullback j f (bettiCmp x))) ∧
      (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration j i).map bettiCmp.toLinearMap =
        A.bettiFiltration j P i) :=
  ⟨A.localAlgebraicComparison, A.projectiveAlgebraicBettiComparison j P,
    fun f => ⟨A.localAlgebraicComparison_naturality f,
      A.projectiveAlgebraicBettiComparison_naturality j P f⟩,
    A.localAlgebraicComparison_filtration, A.projectiveAlgebraicBettiComparison_filtration j P⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
