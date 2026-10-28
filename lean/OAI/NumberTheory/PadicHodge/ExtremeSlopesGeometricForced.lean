import OAI.NumberTheory.PadicHodge.IntrinsicComparison
import OAI.NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

/-! # Extreme Slopes Geometric Forced -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric

/-! Convert the resolved native FrobeniusSlope result on the same coefficient field
and Frobenius into ExtremeSlopes's Hodge-number equality and terminal purity.
The numerical conversion adds no central, cubic or operator hypotheses. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic

/-- Specialize the forced Newton number to the canonical q-adic valuation. -/
theorem newton_of_forced_slope
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {U : Type*} [AddCommGroup U] [Module L U] [Module ℚ_[q] U]
    [IsScalarTower ℚ_[q] L U] [FiniteDimensional L U]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (r b e : AlgebraicClosure ℚ) (f : U ≃ₗ[L] U)
    (h : IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.ForcedSlope (U := U) q L ι r b e f) (he : e ≠ 0) :
    FrobeniusSlopeComparisonNewton.newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) / 3) := by
  have hne := (map_ne_zero ι).mpr he
  have hn := (h (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q) (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_q q)
    (Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e)) (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_apply q (ι e) hne)).2.2.2
  rw [ExtremeSlopesNewtonSummands.CM.Adapter.parameterValuation_eq_canonical q L _ _ _ hne] at hn
  exact hn

/-- Once native FrobeniusSlope fixes the Newton number, only the geometric splitting
and projector data enter the purity conclusion. -/
theorem purity_of_forced_slope
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {U : Type*} [AddCommGroup U] [Module L U] [Module ℚ_[q] U]
    [IsScalarTower ℚ_[q] L U] [FiniteDimensional L U]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (r b e : AlgebraicClosure ℚ) (f : U ≃ₗ[L] U)
    (h : IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.ForcedSlope (U := U) q L ι r b e f) (he : e ≠ 0)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B S : Submodule ℂ W) (hcompl : IsCompl A B)
    (P : Module.End ℂ W) (hRange : LinearMap.range P = S)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B) (hne : S ≠ ⊥)
    (hdim : Module.finrank L U = Module.finrank ℂ S)
    (hcomparison : FrobeniusSlopeComparisonNewton.newton q L U f =
      (Module.finrank ℂ ↥(S ⊓ A) : ℚ))
    (sign : Bool) (initial : ℚ)
    (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial) :
    let slope : ℚ := 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧ (slope = 1 ↔ S ≤ A) ∧ (slope = 0 ↔ S ≤ B) := by
  have hn := newton_of_forced_slope q L ι r b e f h he
  rw [hSign, hdim] at hn
  have hnumber := hcomparison.symm.trans hn
  have hext := IntrinsicPurity.CM.ExtremeSlopesAdapter.extreme_slope_of_sign sign initial (Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e)) hInitial hSign
  rw [hSign] at hext
  refine ⟨hext, ?_⟩
  have hp := ExtremeSlopes.CM.Construction.pure_type_of_extreme_number A B hcompl P hA hB
    (by rwa [hRange]) _ hext (by rwa [hRange])
  simpa only [hRange] using hp

end NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric

namespace NumberTheory.PadicHodge.ExtremeSlopesGeometricForced

/-! Preserve the exact native FrobeniusSlope comparison tuple, and enrich each of
its chosen summands with normalized weak admissibility and Hodge numbers. -/

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic

namespace CM.Adapter.Geometric

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)

def SummandHodgeForced [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
    let χc : H → ℂ := fun h => j (σ (χ h))
    ∃ L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq,
      let S := A.deRhamHeckeSummand ρ χq L
      let B := A.bettiHeckeSummand (j.comp κ) ρ χc
      let F := (GeometricComparison.Linear.finiteCoefficientFiltration L.field Fil).restrict S
      letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
      ∃ φS : S ≃ₗ[L.field] S,
        (∀ x : S, (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
          GeometricComparison.Linear.coefficientFrobenius L.field φdR.toLinearMap (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
        GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L.field Fil S)
          (φS.restrictScalars ℚ_[q]) ∧
        (∀ i : ℤ,
          Module.finrank L.field ↥(S ⊓ GeometricComparison.Linear.coefficientFiltration L.field A.Fil i) =
            Module.finrank ℂ ↥(B ⊓ A.bettiFiltration (j.comp κ) P i)) ∧
        IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.ForcedSlope (U := S) q L.field ι (σ r) (σ b) (σ e) φS ∧
        ExtremeSlopes.CM.Construction.WeaklyAdmissible01 (K := L.field) (D := S) (F.step 1) φS.toLinearMap
          (Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q L.field (V := S) φS) ∧
        Module.finrank L.field S = Module.finrank ℂ B ∧
        F.step 0 = ⊤ ∧ F.step 2 = ⊥ ∧
        Module.finrank L.field (F.step 1) = Module.finrank ℂ ↥(B ⊓ A.bettiFiltration (j.comp κ) P 1) ∧
        FrobeniusSlopeComparisonNewton.newton q L.field S φS =
          (Module.finrank ℂ ↥(B ⊓ A.bettiFiltration (j.comp κ) P 1) : ℚ) ∧
        FrobeniusSlopeComparisonNewton.newton q L.field S φS = (Module.finrank L.field S : ℚ) *
          (1 / 2 - Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι (σ e)) / 3)

theorem hodge_numbers_on_forced_summands [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (hFil : Fil.step = A.Fil)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ) (he : e ≠ 0)
    (h : IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.SummandForced A κ j ι ρ P Fil φdR χ r b e) :
    SummandHodgeForced A κ j ι ρ P Fil φdR χ r b e := by
  intro σ
  obtain ⟨L, φS, hincl, hWA, hcmp, hforced⟩ := h σ
  let S := A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L
  let : AddCommGroup S := inferInstance
  let : Module L.field S := inferInstance
  let : Module ℚ_[q] S := inferInstance
  let : Module.Free L.field S := inferInstance
  have hn := GeometricComparisonAdapter.CM.ExtremeSlopes.summand_comparison_numbers A (j.comp κ) H ρ P
    (fun h => ι (σ (χ h))) (fun h => j (σ (χ h))) L Fil hFil φS hWA hcmp
  refine ⟨L, φS, hincl, hWA, hcmp, hforced,
    Filtration.CM.ExtremeSlopesAdapter.coefficient_weaklyAdmissible01 q L.field Fil _ φS hWA hn.2.1 hn.2.2.1,
    hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, ?_, ?_⟩
  · exact ExtremeSlopesNewtonSummands.CM.Adapter.intrinsic_newton_eq_hodge_of_comparison q L.field (V := S) φS _ hn.2.2.2.2
  · exact newton_of_forced_slope q (U := S) L.field ι (σ r) (σ b) (σ e) φS hforced
      ((map_ne_zero σ).mpr he)

/-- Every full GeometricComparison clause is retained on this one comparison witness. -/
def ComparisonHodgeForced
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      let := hD
      let := hC
      ∃ hB : FiniteDimensional ℂ (A.ComplexBetti (j.comp κ)),
      let := hB
      ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
        (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
        (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
        φ.toLinearMap = A.crystallineFrobenius ∧ Fil.step = A.Fil ∧
        let φdR := cmp.symm.trans (φ.trans cmp)
        GeometricComparison.Linear.WeaklyAdmissible q Fil φdR ∧
        (∀ f : A.ExtendingEndomorphism,
          (∀ x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) ∧
          (∀ x, φ (A.crystallinePullback f x) = A.crystallinePullback f (φ x)) ∧
          (∀ i : ℤ, (A.Fil i).map (A.deRhamPullback f) ≤ A.Fil i)) ∧
        (∃ W : Polynomial ℤ,
          A.IsWeilPolynomial ℓ W ∧
          LinearMap.charpoly A.crystallineFrobenius = W.map (Int.castRingHom ℚ_[q]) ∧
          ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ)) ∧
        (∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
          (bettiCmp : A.ComplexAlgebraicDeRham (j.comp κ) ≃ₗ[ℂ] A.ComplexBetti (j.comp κ)),
          (∀ f : A.ExtendingEndomorphism,
            (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
            (∀ x, bettiCmp (A.complexAlgebraicPullback (j.comp κ) f x) =
              A.complexBettiPullback (j.comp κ) f (bettiCmp x))) ∧
          (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
          (∀ i : ℤ, (A.complexAlgebraicFiltration (j.comp κ) i).map bettiCmp.toLinearMap =
            A.bettiFiltration (j.comp κ) P i)) ∧
        GeometricComparison.HeckeScalar.SummandComparison q κ j ι jq A H ρ P Fil φdR ∧
        SummandHodgeForced A κ j ι ρ P Fil φdR χ r b e

theorem comparison_add_hodge_numbers
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ) (he : e ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h : IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced A κ j ι ρ P χ r b e ℓ) :
    ComparisonHodgeForced A κ j ι ρ P χ r b e ℓ := by
  obtain ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm, hforced⟩ := h
  let := hD
  let := hC
  obtain ⟨localCmp, bettiCmp, hlocal⟩ := hbase
  have hB := GeometricComparisonAdapter.CM.ExtremeSlopes.complex_finite_of_comparisons A (j.comp κ) localCmp bettiCmp
  refine ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW,
    ⟨localCmp, bettiCmp, hlocal⟩, hsumm, ?_⟩
  exact hodge_numbers_on_forced_summands A κ j ι ρ P Fil _ hFil χ r b e he hforced

end CM.Adapter.Geometric

end NumberTheory.PadicHodge.ExtremeSlopesGeometricForced

namespace NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric
open OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic
section

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)

/-- Recover the original native FrobeniusSlope summands with their exact witnesses. -/
theorem forget_summand_hodge [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (h : SummandHodgeForced A κ j ι ρ P Fil φdR χ r b e) :
    IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.SummandForced A κ j ι ρ P Fil φdR χ r b e := by
  intro σ
  obtain ⟨L, φS, hi, hWA, hcmp, hf, _⟩ := h σ
  exact ⟨L, φS, hi, hWA, hcmp, hf⟩

/-- Forgetting only the added Hodge numbers recovers the entire native
FrobeniusSlope comparison, including all original GeometricComparison conclusions. -/
theorem forget_comparison_hodge
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ComparisonHodgeForced A κ j ι ρ P χ r b e ℓ) :
    IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced A κ j ι ρ P χ r b e ℓ := by
  obtain ⟨hD, hC, _hB, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm, hf⟩ := h
  let := hD
  let := hC
  exact ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm,
    forget_summand_hodge A κ j ι ρ P Fil _ χ r b e hf⟩

end

section

/-! Terminal ExtremeSlopes purity on the actual character. The native comparison
has already discharged all scalar, commutation, weight and cubic inputs. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)

def CharacterPurity (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (slope : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℚ) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    let S := A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (σ (χ h)))
    let F1 := A.bettiFiltration (j.comp κ) P 1
    ∀ (B : Submodule ℂ (A.ComplexBetti (j.comp κ))), IsCompl F1 B →
    ∀ (projector : Module.End ℂ (A.ComplexBetti (j.comp κ))),
      LinearMap.range projector = S →
      (∀ x ∈ F1, projector x ∈ F1) →
      (∀ x ∈ B, projector x ∈ B) → S ≠ ⊥ →
      (slope σ = 0 ∨ slope σ = 1) ∧ (slope σ = 1 ↔ S ≤ F1) ∧ (slope σ = 0 ↔ S ≤ B)

/-- Apply the proved Hodge-number identity on the coefficient field chosen
by native FrobeniusSlope. Sign inputs here are supplied by the retained root wrapper. -/
theorem character_purity_of_comparison
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ComparisonHodgeForced A κ j ι ρ P χ r b e ℓ)
    (sign : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Bool) (initial : ℚ)
    (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι (σ e)) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial) :
    CharacterPurity A κ j ρ P χ (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3) := by
  obtain ⟨hD, hC, hB, cmp, φ, Fil, _hφ, _hFil, _hWA, _hfun, _hW, _hbase, _hsumm, hf⟩ := h
  let := hD
  let := hC
  let := hB
  intro σ S F1 B hcompl projector hRange hA hBpres hne
  obtain ⟨L, φS, _hi, _hWAS, _hcmp, _hforced, _hWA01, hdim, _h0, _h2, _h1, hn, hval⟩ := hf σ
  rw [hdim, hSign σ] at hval
  have hnumber := hn.symm.trans hval
  have hext := IntrinsicPurity.CM.ExtremeSlopesAdapter.extreme_slope_of_sign (sign σ) initial (Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι (σ e)))
    hInitial (hSign σ)
  rw [hSign σ] at hext
  refine ⟨hext, ?_⟩
  have hp := ExtremeSlopes.CM.Construction.pure_type_of_extreme_number (A.bettiFiltration (j.comp κ) P 1)
    B hcompl projector hA hBpres (by rwa [hRange]) _ hext (by rwa [hRange])
  simpa only [hRange] using hp

end

/-! Abstract the parameter tuple before instantiating the large native model.
This keeps kernel checking independent of unfolding geometric realizations. -/

open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)
  (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (idx : Fin 3 → H) (r a : AlgebraicClosure ℚ)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (sign : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Bool) (initial : ℚ)

theorem parameter_comparison_add_purity
    (ha : a ≠ 0) (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι (σ a)) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial)
    (h : ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced A κ j ι ρ P χ r b a ℓ) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      ComparisonHodgeForced A κ j ι ρ P χ r b a ℓ ∧
      CharacterPurity A κ j ρ P χ
        (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3) := by
  obtain ⟨b, hb, hc, hv, hcomp⟩ := h
  have hh := comparison_add_hodge_numbers A κ j ι ρ P χ r b a ha ℓ hcomp
  exact ⟨b, hb, hc, hv, hh,
    character_purity_of_comparison A κ j ι ρ P χ r b a ℓ hh sign initial hInitial hSign⟩

theorem forget_parameter_comparison_purity
    (h : ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      ComparisonHodgeForced A κ j ι ρ P χ r b a ℓ ∧
      CharacterPurity A κ j ρ P χ
        (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3)) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced A κ j ι ρ P χ r b a ℓ := by
  obtain ⟨b, hb, hc, hv, hh, _⟩ := h
  exact ⟨b, hb, hc, hv, forget_comparison_hodge A κ j ι ρ P χ r b a ℓ hh⟩

end NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric

end

end OAI
