import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoFiltrationGeneral
import OAI.NumberTheory.PadicHodge.GeometricComparison.Betti

/-! # Abelian Global Filtered Comparisons -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Local and fixed-complex filtered comparisons from the same original number-field de Rham object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Geometry.AbelianH1Model.filtered_trans {F M N T : Type*} [CommRing F]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
    [Module F M] [Module F N] [Module F T]
    (e : M ≃ₗ[F] N) (d : N ≃ₗ[F] T) (P : Submodule F M) (Q : Submodule F N) (W : Submodule F T)
    (h₁ : P.map e.toLinearMap = Q) (h₂ : Q.map d.toLinearMap = W) :
    P.map (e.trans d).toLinearMap = W :=
  (Submodule.map_comp e.toLinearMap d.toLinearMap P).trans
    ((congrArg (Submodule.map d.toLinearMap) h₁).trans h₂)

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.localAlgebraicComparison : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham := by
  letI : Algebra K ℚ_[q] := jq.toAlgebra
  exact (IntrinsicPullbackScalarExtension.equiv K ℚ_[q] A.variety.scheme 1).trans
    (GeometricComparison.DeRham.IsoCohomology.isoPullback A.genericIso.hom 1)

theorem Geometry.AbelianH1Model.localAlgebraicComparison_filtration (r : ℤ) :
    (A.localAlgebraicFiltration r).map A.localAlgebraicComparison.toLinearMap = A.Fil r := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let e := IntrinsicPullbackScalarExtension.equiv K ℚ_[q] A.variety.scheme 1
  let d := GeometricComparison.DeRham.IsoCohomology.isoPullback A.genericIso.hom 1
  have h₁ := IntrinsicPullbackScalarExtension.equiv_filtration K ℚ_[q] A.variety.scheme 1 r
  have h₂ := GeometricComparison.DeRham.IsoFiltrationGeneral.isoPullback_filtration_without_finiteness A.genericIso.hom 1 r
  exact (Submodule.map_comp e.toLinearMap d.toLinearMap (A.localAlgebraicFiltration r)).trans
    ((congrArg (Submodule.map d.toLinearMap) h₁).trans h₂)

def Geometry.AbelianH1Model.complexAlgebraicComparison (j : K →+* ℂ) : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 := by
  letI : Algebra K ℂ := j.toAlgebra
  exact IntrinsicPullbackScalarExtension.equiv K ℂ A.variety.scheme 1

theorem Geometry.AbelianH1Model.complexAlgebraicComparison_filtration (j : K →+* ℂ) (r : ℤ) :
    (A.complexAlgebraicFiltration j r).map (A.complexAlgebraicComparison j).toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r := by
  let : Algebra K ℂ := j.toAlgebra
  exact IntrinsicPullbackScalarExtension.equiv_filtration K ℂ A.variety.scheme 1 r

def Geometry.AbelianH1Model.algebraicBettiComparison (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ) :
    A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j :=
  (A.complexAlgebraicComparison j).trans (A.nativeComplexComparison hBettiComparison j)

theorem Geometry.AbelianH1Model.algebraicBettiComparison_filtration (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) (r : ℤ) :
    (A.complexAlgebraicFiltration j r).map (A.algebraicBettiComparison hBettiComparison j).toLinearMap =
      A.bettiFiltration j P r := by
  let e : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 :=
    A.complexAlgebraicComparison j
  let d : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 ≃ₗ[ℂ] A.ComplexBetti j :=
    A.nativeComplexComparison hBettiComparison j
  have h₁ : (A.complexAlgebraicFiltration j r).map e.toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r :=
    A.complexAlgebraicComparison_filtration j r
  have h₂ : (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r).map d.toLinearMap =
      A.bettiFiltration j P r := A.nativeComplexComparison_filtration hBettiComparison j P r
  exact Geometry.AbelianH1Model.filtered_trans e d (A.complexAlgebraicFiltration j r)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r) (A.bettiFiltration j P r) h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
