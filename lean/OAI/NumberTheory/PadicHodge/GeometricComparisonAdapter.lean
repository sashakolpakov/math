import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton
import OAI.NumberTheory.PadicHodge.Filtration
import Mathlib.RingTheory.Finiteness.Descent

/-! # Geometric Comparison Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparisonAdapter

noncomputable section

/-! Exact GeometricComparison input and its induced geometric summand data for ExtremeSlopes.
The main GeometricComparison proposition is assumed explicitly, never imported as a theorem.
-/

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

namespace CM.ExtremeSlopes

open OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-- The full repaired GeometricComparison proposition, including its geometric hypotheses. -/
def GeometricComparisonInput : Prop := ∀
    (K : Type) [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (_hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓq : ℓ ≠ q),
    GeometricComparison.HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ

variable {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

/-- The first Betti filtration step is the actual holomorphic subspace. -/
theorem betti_filtration_one
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    A.bettiFiltration j P 1 = (A.smoothProjectiveFiber j P).pureBettiSubspace 1 0 := rfl

/-- Finite dimension descends through the local scalar extension and then
extends to the fixed complex fiber, using GeometricComparison's two actual comparisons. -/
theorem complex_finite_of_comparisons
    [FiniteDimensional ℚ_[q] A.DeRham]
    (j : K →+* ℂ)
    (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (bettiCmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j) :
    FiniteDimensional ℂ (A.ComplexBetti j) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K ℂ := j.toAlgebra
  have : FiniteDimensional ℚ_[q] A.LocalAlgebraicDeRham :=
    FiniteDimensional.of_injective localCmp.toLinearMap localCmp.injective
  have : Module.Finite K A.AlgebraicDeRham :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℚ_[q]
  exact FiniteDimensional.of_surjective bettiCmp.toLinearMap bettiCmp.surjective

/-- A GeometricComparison summand comparison determines the whole and first-step dimensions,
the endpoint filtration conditions, and the unnormalized rational Newton number. -/
theorem summand_comparison_numbers
    [FiniteDimensional ℚ_[q] A.DeRham]
    (j : K →+* ℂ)
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left
      (A.complexFiber j).scheme.hom)
    (χq : H → AlgebraicClosure ℚ_[q]) (χc : H → ℂ)
    (L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq)
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (hFil : Fil.step = A.Fil)
    (φS : A.deRhamHeckeSummand ρ χq L ≃ₗ[L.field] A.deRhamHeckeSummand ρ χq L)
    (hWA : letI : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χq L) :=
        Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χq L)
      GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L.field Fil
        (A.deRhamHeckeSummand ρ χq L)) (φS.restrictScalars ℚ_[q]))
    (hcmp : ∀ i : ℤ,
      Module.finrank L.field ↥(A.deRhamHeckeSummand ρ χq L ⊓
        GeometricComparison.Linear.coefficientFiltration L.field A.Fil i) =
      Module.finrank ℂ ↥(A.bettiHeckeSummand j ρ χc ⊓ A.bettiFiltration j P i)) :
    let S := A.deRhamHeckeSummand ρ χq L
    let B := A.bettiHeckeSummand j ρ χc
    let F := (GeometricComparison.Linear.finiteCoefficientFiltration L.field Fil).restrict S
    Module.finrank L.field S = Module.finrank ℂ B ∧
    F.step 0 = ⊤ ∧ F.step 2 = ⊥ ∧
    Module.finrank L.field (F.step 1) =
      Module.finrank ℂ ↥(B ⊓ A.bettiFiltration j P 1) ∧
    (Padic.valuation (p := q) (LinearMap.det (A := ℚ_[q]) (M := A.deRhamHeckeSummand ρ χq L)
      (φS.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
      (Module.finrank ℚ_[q] L.field : ℚ) *
        (Module.finrank ℂ ↥(B ⊓ A.bettiFiltration j P 1) : ℚ) := by
  apply Filtration.CM.ExtremeSlopesAdapter.coefficient_comparison_numbers q L.field Fil
    (A.deRhamHeckeSummand ρ χq L) (A.bettiHeckeSummand j ρ χc)
    (A.bettiFiltration j P) φS hWA (fun i hi => ite_eq_left hi) (by rfl)
  intro i
  rw [hFil]
  exact hcmp i

/-- The arithmetic data extracted from GeometricComparison for every coefficient-conjugate
character, with the actual induced filtration and Frobenius. -/
def NativeSummandComparison
    [FiniteDimensional ℚ_[q] A.DeRham]
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham) : Prop :=
  ∀ χ : H →ₐ[ℚ] AlgebraicClosure ℚ,
    A.bettiHeckeSummand (jComplex.comp κ) ρ (fun h => jComplex (χ h)) ≠ ⊥ →
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
      let χc : H → ℂ := fun h => jComplex (σ (χ h))
      ∃ L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq,
        let S := A.deRhamHeckeSummand ρ χq L
        let B := A.bettiHeckeSummand (jComplex.comp κ) ρ χc
        let F := (GeometricComparison.Linear.finiteCoefficientFiltration L.field Fil).restrict S
        letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
        ∃ φS : S ≃ₗ[L.field] S,
          (∀ x : S, (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
            GeometricComparison.Linear.coefficientFrobenius L.field φdR.toLinearMap
              (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
          GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L.field Fil S)
            (φS.restrictScalars ℚ_[q]) ∧
          (∀ a : AlgebraicClosure ℚ,
            Module.End.HasEigenvalue
              (φS.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (ι a) →
                ‖jComplex a‖ = Real.sqrt (q : ℝ)) ∧
          ExtremeSlopes.CM.Construction.WeaklyAdmissible01 (K := L.field) (D := S) (F.step 1) φS.toLinearMap
            (Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q L.field (V := S) φS) ∧
          Module.finrank L.field S = Module.finrank ℂ B ∧
          F.step 0 = ⊤ ∧ F.step 2 = ⊥ ∧
          Module.finrank L.field (F.step 1) =
            Module.finrank ℂ ↥(B ⊓
              A.bettiFiltration (jComplex.comp κ) P 1) ∧
          (Padic.valuation (p := q)
            (LinearMap.det (A := ℚ_[q]) (M := S)
              (φS.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
            (Module.finrank ℚ_[q] L.field : ℚ) *
              (Module.finrank ℂ ↥(B ⊓
                A.bettiFiltration (jComplex.comp κ) P 1) : ℚ)

/-- Adapter from the FULL repaired GeometricComparison proposition. Finiteness, comparisons,
and weak admissibility are obtained from its conclusion. The rational Hodge
number and all filtration identifications are then derived. -/
theorem native_summands_of_full_GeometricComparison
    (h_GeometricComparison : GeometricComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
    ∃ hB : FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ)),
      letI := hD
      letI := hC
      letI := hB
      ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
        (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
        (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
        φ.toLinearMap = A.crystallineFrobenius ∧ Fil.step = A.Fil ∧
        NativeSummandComparison A κ jComplex ι H ρ P Fil
          (cmp.symm.trans (φ.trans cmp)) := by
  obtain ⟨hD, hC, hc⟩ := h_GeometricComparison K q κ jComplex ι jq hplace A H ρ P ℓ hℓq
  let := hD
  let := hC
  obtain ⟨cmp, φ, Fil, hφ, hFil, _hWA, _hfun, _hweil, hgeo, hsumm⟩ := hc
  obtain ⟨localCmp, bettiCmp, _hgeo⟩ := hgeo
  have hB := complex_finite_of_comparisons A (jComplex.comp κ) localCmp bettiCmp
  refine ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, ?_⟩
  obtain ⟨W, _hW, hchar, hweight⟩ := _hweil
  let φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham := cmp.symm.trans (φ.trans cmp)
  have hdRchar : φdR.toLinearMap.charpoly = W.map (Int.castRingHom ℚ_[q]) := by
    change LinearMap.charpoly (cmp.conj φ.toLinearMap) = _
    rw [LinearEquiv.charpoly_conj, hφ, hchar]
  intro χ hχ σ
  obtain ⟨L, φS, hφS, hWAS, hcompS⟩ := hsumm χ hχ σ
  refine ⟨L, φS, hφS, hWAS, ?_, ?_⟩
  · intro a ha
    exact FrobeniusSlopeComparisonNewton.weights_on_baseChanged_subspace
      φdR.toLinearMap W hdRchar q hweight
      (A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L) φS.toLinearMap
      hφS jComplex ι a ha
  have hn := summand_comparison_numbers A (jComplex.comp κ) H ρ P
    (fun h => ι (σ (χ h))) (fun h => jComplex (σ (χ h)))
    L Fil hFil φS hWAS hcompS
  exact ⟨Filtration.CM.ExtremeSlopesAdapter.coefficient_weaklyAdmissible01 q L.field Fil _ φS hWAS hn.2.1 hn.2.2.1, hn⟩

end CM.ExtremeSlopes

end

end OAI.NumberTheory.PadicHodge.GeometricComparisonAdapter
