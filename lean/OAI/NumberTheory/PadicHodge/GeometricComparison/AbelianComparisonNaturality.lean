import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianGlobalFilteredComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PullbackScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Betti
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor

/-! # Abelian Comparison Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The actual local and complex algebraic comparisons intertwine every extending geometric endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.localAlgebraicComparison_naturality (f : A.ExtendingEndomorphism) (x : A.LocalAlgebraicDeRham) :
    A.localAlgebraicComparison (A.localAlgebraicPullback f x) =
      A.deRhamPullback f (A.localAlgebraicComparison x) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let e := IntrinsicPullbackScalarExtension.equiv K ℚ_[q] A.variety.scheme 1
  let d := GeometricComparison.DeRham.IsoCohomology.isoPullback A.genericIso.hom 1
  let g := (Over.pullback (Geometry.scalarBaseMap jq)).map f.generic.toMul.hom.hom
  have h₁ := Intrinsic.PullbackScalarNaturality.IntrinsicPullbackScalarExtension.naturality K ℚ_[q] f.generic.toMul.hom.hom 1 x
  have h₂ := GeometricComparison.DeRham.Functor.pullback_square (A.localEndomorphism f) g A.genericIso.hom A.genericIso.hom f.compatible 1
  have hd : d.toLinearMap = GeometricComparison.DeRham.Int.pullback A.genericIso.hom 1 := GeometricComparison.DeRham.IsoCohomology.isoPullback_toLinearMap A.genericIso.hom 1
  have hmap (z : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℚ_[q]
      ((Over.pullback (Geometry.scalarBaseMap jq)).obj A.variety.scheme) 1) :
      d (GeometricComparison.DeRham.Int.pullback g 1 z) = A.deRhamPullback f (d z) := by
    change d.toLinearMap (GeometricComparison.DeRham.Int.pullback g 1 z) = A.deRhamPullback f (d.toLinearMap z)
    rw [hd]
    exact LinearMap.congr_fun h₂.symm z
  exact (congrArg d h₁).trans (hmap (e x))

theorem Geometry.AbelianH1Model.complexAlgebraicComparison_naturality (j : K →+* ℂ) (f : A.ExtendingEndomorphism)
    (x : A.ComplexAlgebraicDeRham j) :
    A.complexAlgebraicComparison j (A.complexAlgebraicPullback j f x) =
      GeometricComparison.DeRham.Int.pullback (A.complexEndomorphism j f) 1 (A.complexAlgebraicComparison j x) := by
  let : Algebra K ℂ := j.toAlgebra
  exact Intrinsic.PullbackScalarNaturality.IntrinsicPullbackScalarExtension.naturality K ℂ f.generic.toMul.hom.hom 1 x

end

section

/-! The actual algebraic-to-Betti comparison commutes with every extending geometric endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Geometry.AbelianH1Model.comparison_trans_naturality {F M N T : Type*} [CommRing F]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T] [Module F M] [Module F N] [Module F T]
    (e : M ≃ₗ[F] N) (d : N ≃ₗ[F] T) (a : M →ₗ[F] M) (b : N →ₗ[F] N) (c : T →ₗ[F] T)
    (he : ∀ x, e (a x) = b (e x)) (hd : ∀ y, d (b y) = c (d y)) (x : M) :
    (e.trans d) (a x) = c ((e.trans d) x) :=
  (congrArg d (he x)).trans (hd (e x))

theorem Geometry.AbelianH1Model.comparison_naturality_apply {F N T : Type*} [CommRing F]
    [AddCommGroup N] [AddCommGroup T] [Module F N] [Module F T]
    (d : N ≃ₗ[F] T) (b : N →ₗ[F] N) (c : T →ₗ[F] T)
    (h : d.toLinearMap.comp b = c.comp d.toLinearMap) (z : N) : d (b z) = c (d z) :=
  LinearMap.congr_fun h z

theorem Geometry.AbelianH1Model.comparison_trans_exists {F M N T I J : Type*} [CommRing F]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T] [Module F M] [Module F N] [Module F T]
    (e : M ≃ₗ[F] N) (d : N ≃ₗ[F] T)
    (a : I → Module.End F M) (b : I → Module.End F N) (c : I → Module.End F T)
    (P : J → Submodule F M) (Q : J → Submodule F N) (W : J → Submodule F T)
    (he : ∀ i x, e (a i x) = b i (e x))
    (hd : ∀ i, d.toLinearMap.comp (b i) = (c i).comp d.toLinearMap)
    (hP : ∀ j, (P j).map e.toLinearMap = Q j) (hQ : ∀ j, (Q j).map d.toLinearMap = W j) :
    ∃ cmp : M ≃ₗ[F] T, (∀ i x, cmp (a i x) = c i (cmp x)) ∧
      (∀ j, (P j).map cmp.toLinearMap = W j) :=
  ⟨e.trans d, fun i => Geometry.AbelianH1Model.comparison_trans_naturality e d (a i) (b i) (c i) (he i)
      (Geometry.AbelianH1Model.comparison_naturality_apply d (b i) (c i) (hd i)),
    fun j => Geometry.AbelianH1Model.filtered_trans e d (P j) (Q j) (W j) (hP j) (hQ j)⟩

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.algebraicBettiComparison_exists (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    ∃ cmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j,
      (∀ f : A.ExtendingEndomorphism, ∀ x,
        cmp (A.complexAlgebraicPullback j f x) = A.complexBettiPullback j f (cmp x)) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration j i).map cmp.toLinearMap = A.bettiFiltration j P i) := by
  let : Algebra K ℂ := j.toAlgebra
  let e : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ]
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 :=
    A.complexAlgebraicComparison j
  let d : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 ≃ₗ[ℂ] A.ComplexBetti j :=
    A.nativeComplexComparison hBettiComparison j
  have hn (f : A.ExtendingEndomorphism) : d.toLinearMap.comp (GeometricComparison.DeRham.Int.pullback (A.complexEndomorphism j f) 1) =
      (A.complexBettiPullback j f).comp d.toLinearMap :=
    Betti.ComplexComparison.nativeEquiv_naturality hBettiComparison
      (X := (A.complexFiber j).scheme) (Y := (A.complexFiber j).scheme) (A.complexEndomorphism j f) 1
  have hP (i : ℤ) : (A.complexAlgebraicFiltration j i).map e.toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 i :=
    A.complexAlgebraicComparison_filtration j i
  have hQ (i : ℤ) : (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 i).map d.toLinearMap =
      A.bettiFiltration j P i := A.nativeComplexComparison_filtration hBettiComparison j P i
  exact Geometry.AbelianH1Model.comparison_trans_exists (F := ℂ) (M := A.ComplexAlgebraicDeRham j)
    (N := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1)
    (T := A.ComplexBetti j) (I := A.ExtendingEndomorphism) (J := ℤ) e d (A.complexAlgebraicPullback j)
    (fun f => GeometricComparison.DeRham.Int.pullback (A.complexEndomorphism j f) 1) (A.complexBettiPullback j)
    (A.complexAlgebraicFiltration j)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1)
    (A.bettiFiltration j P) (A.complexAlgebraicComparison_naturality j) hn
    hP hQ

end

/-! The exact local-and-Betti comparison clause required in the GeometricComparison target, with geometric endomorphism and native filtration compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.algebraic_filtered_comparisons (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    ∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
      (bettiCmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j),
      (∀ f : A.ExtendingEndomorphism,
        (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
        (∀ x, bettiCmp (A.complexAlgebraicPullback j f x) = A.complexBettiPullback j f (bettiCmp x))) ∧
      (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration j i).map bettiCmp.toLinearMap = A.bettiFiltration j P i) := by
  obtain ⟨bettiCmp, hnat, hfil⟩ := A.algebraicBettiComparison_exists hBettiComparison j P
  exact ⟨A.localAlgebraicComparison, bettiCmp,
    fun f => ⟨A.localAlgebraicComparison_naturality f, hnat f⟩,
    A.localAlgebraicComparison_filtration, hfil⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
