import OAI.NumberTheory.PadicHodge.GeometricComparison
import OAI.NumberTheory.PadicHodge.IntrinsicPurity

/-! # Extreme Slopes Newton Summands -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter

/-!
# ExtremeSlopes with the verified FrobeniusSlope Newton adapter

Reuse the complete GeometricComparison/Newton witnesses and their intrinsic norm-defined
Newton number. The valuation in the constructed finite parameter field is
proved equal to the canonical valuation used by the full GaloisValuation adapter.
RadialDilation, CubicRelation, CentralConstraint, commutation, Commuting and valuation hypotheses remain explicit.
No arbitrary projector or operator is identified with a geometric action.
-/

open scoped TensorProduct

/-- The two Newton interfaces use exactly the same rational determinant. -/
theorem normalized_newton_top_eq_intrinsic
    (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module ℚ_[q] V]
    [IsScalarTower ℚ_[q] L V] [FiniteDimensional L V] (f : V ≃ₗ[L] V) :
    Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q L f ⊤ = FrobeniusSlopeComparisonNewton.newton q L V f := by
  simp [Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton, Filtration.CM.ExtremeSlopesAdapter.summandNewton, FrobeniusSlopeComparisonNewton.newton]

/-- The finite norm-defined valuation equals the canonical p-adic valuation. -/
theorem intrinsic_localValuation_eq_canonical
    (q : ℕ) [Fact q.Prime]
    {L : Type*} [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    (j : L →ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q]) (x : L) (hx : x ≠ 0) :
    FrobeniusSlopeComparisonNewton.localValuation q L x = Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j x) := by
  have hd : (Module.finrank ℚ_[q] L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  unfold FrobeniusSlopeComparisonNewton.localValuation
  rw [Valuation.CM.ExtremeSlopesAdapter.valuation_norm q j x hx]
  field_simp

/-- In particular, the parameter field constructed by FrobeniusSlope computes precisely
GaloisValuation's canonical parameter valuation; the extra generators have no effect. -/
theorem parameterValuation_eq_canonical
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    (r b e : AlgebraicClosure ℚ_[q]) (he : e ≠ 0) :
    FrobeniusSlopeComparisonNewton.parameterValuation q L r b e = Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q e := by
  let M := FrobeniusSlopeComparisonNewton.parameterField q L r b e
  let eM : M := ⟨e, (FrobeniusSlopeComparisonNewton.parameters_mem_parameterField q L r b e).2.2⟩
  have heM : eM ≠ 0 := fun hz => he (congrArg Subtype.val hz)
  exact intrinsic_localValuation_eq_canonical q (M.val.restrictScalars ℚ_[q]) eM heM

/-- The normalized Newton function is unchanged by finite coefficient enlargement. -/
theorem normalized_newton_top_baseChange
    (q : ℕ) [Fact q.Prime]
    (L M V : Type*) [Field L] [Field M]
    [Algebra ℚ_[q] L] [Algebra ℚ_[q] M] [Algebra L M]
    [IsScalarTower ℚ_[q] L M]
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional L M] [FiniteDimensional ℚ_[q] M]
    [AddCommGroup V] [Module L V] [Module ℚ_[q] V]
    [IsScalarTower ℚ_[q] L V] [FiniteDimensional L V]
    (f : V ≃ₗ[L] V) :
    Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q M (f.baseChange L M V V) ⊤ =
      Filtration.CM.ExtremeSlopesAdapter.normalizedSummandNewton q L f ⊤ := by
  rw [normalized_newton_top_eq_intrinsic, normalized_newton_top_eq_intrinsic]
  exact FrobeniusSlopeComparisonNewton.newton_baseChange q L M V f

/-- Extending the coefficient field preserves the dimension of each
induced filtration step over its respective coefficient field. -/
theorem enlarged_filtration_step_finrank
    {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (M : Type*) [Field M] [Algebra L M]
    (F : GeometricComparison.Linear.FiniteFiltration L V) (i : ℤ) :
    Module.finrank M ((GeometricComparison.Linear.finiteCoefficientFiltration M F).step i) =
      Module.finrank L (F.step i) := by
  change Module.finrank M ((F.step i).baseChange M) = _
  have hi : Function.Injective ((F.step i).subtype.baseChange M) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (F.step i).subtype (F.step i).injective_subtype
  rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hi, Module.finrank_baseChange]

/-- The Hodge number is invariant under finite coefficient enlargement;
restriction back to the base field is handled by the already proved degree factor. -/
theorem enlarged_filtration_hodge_number
    {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (M : Type*) [Field M] [Algebra L M]
    (F : GeometricComparison.Linear.FiniteFiltration L V) :
    (GeometricComparison.Linear.finiteCoefficientFiltration M F).tH = F.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  congr 1
  funext i
  congr 1
  rw [WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.graded_finrank_eq_sub,
    WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.graded_finrank_eq_sub,
    enlarged_filtration_step_finrank, enlarged_filtration_step_finrank]

/-- GeometricComparison's rational Hodge comparison gives the intrinsic normalized Newton
number, by cancellation of the positive coefficient degree. -/
theorem intrinsic_newton_eq_hodge_of_comparison
    (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module ℚ_[q] V]
    [IsScalarTower ℚ_[q] L V] [FiniteDimensional L V]
    (f : V ≃ₗ[L] V) (hodge : ℚ)
    (hcomparison :
      (Padic.valuation (p := q) (LinearMap.det (f.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
        (Module.finrank ℚ_[q] L : ℚ) * hodge) :
    FrobeniusSlopeComparisonNewton.newton q L V f = hodge := by
  have hd : (Module.finrank ℚ_[q] L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  unfold FrobeniusSlopeComparisonNewton.newton
  change (Padic.valuation (p := q) (LinearMap.det (f.restrictScalars ℚ_[q]).toLinearMap) : ℚ) /
    (Module.finrank ℚ_[q] L : ℚ) = hodge
  rw [hcomparison]
  field_simp

/-- Reuse the verified intrinsic Newton theorem with all residual graph inputs
explicit, and identify its constructed parameter valuation with the one used
by `signs_of_full_GaloisValuation`. -/
theorem intrinsic_newton_with_GaloisValuation_valuation
    (q : ℕ) [Fact q.Prime]
    {K U : Type*} [Field K] [CharZero K]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U]
    (jC : K →+* ℂ) (ι : K →+* AlgebraicClosure ℚ_[q]) (f : U ≃ₗ[L] U)
    (hdata : FrobeniusSlopeComparisonNewton.NewtonData (L := L) (U := U) q jC ι f)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (hCubicRelation :
      (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 3 - T 0 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q]))) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hCommuting : FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ)) (hνq : ν (q : (AlgebraicClosure ℚ_[q])) = 1)
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ)) :
    FrobeniusSlopeComparisonNewton.newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) / 3) := by
  have hn := FrobeniusSlopeComparisonNewton.intrinsic_newton_on_coefficient_field
    q L jC ι f hdata r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm
    hCubicRelation hCentralConstraint_satake hCommuting ν hνq s hνe
  have he : e ≠ 0 := by
    intro he
    simp [he] at hRadialDilation
  rw [parameterValuation_eq_canonical q L (ι r) (ι b) (ι e) ((map_ne_zero ι).mpr he)] at hn
  exact hn

end NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter

namespace NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

/-!
Retain the full verified GeometricComparison/Newton comparison and upgrade its SAME actual
coefficient-conjugate witnesses with ExtremeSlopes's induced filtration endpoints,
normalized weak admissibility, and first-step Hodge dimension. No projector
or operator realization is assumed here.
-/

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

namespace CM.Adapter

variable {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

/-- Native comparison together with the verified conditional NewtonData. -/
def VerifiedNativeSummandComparison
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
          FrobeniusSlopeComparisonNewton.NewtonData (L := L.field) (U := S) q jComplex ι φS ∧
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
                A.bettiFiltration (jComplex.comp κ) P 1) : ℚ) ∧
          FrobeniusSlopeComparisonNewton.newton q L.field S φS =
            (Module.finrank ℂ ↥(B ⊓ A.bettiFiltration (jComplex.comp κ) P 1) : ℚ)

/-- Apply the verified full-input FrobeniusSlope/GeometricComparison adapter and preserve all of its
conclusions, then derive the ExtremeSlopes numerical data on its genuine summands. -/
theorem verified_native_summands_of_full_GeometricComparison
    (h_GeometricComparison : GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    GeometricComparison.FrobeniusSlope.ComparisonWithNewton q κ jComplex ι jq A H ρ P ℓ ∧
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
        VerifiedNativeSummandComparison A κ jComplex ι H ρ P Fil
          (cmp.symm.trans (φ.trans cmp)) := by
  have hfull := GeometricComparison.FrobeniusSlope.comparison_with_newton_from_full_GeometricComparison
    q κ jComplex ι jq A H ρ P (@h_GeometricComparison) hplace ℓ hℓq
  refine ⟨hfull, ?_⟩
  obtain ⟨hD, hC, hcomp⟩ := hfull
  let := hD
  let := hC
  obtain ⟨cmp, φ, Fil, hφ, hFil, _hWA, _hfun, _hweil, hgeo, hsumm⟩ := hcomp
  obtain ⟨localCmp, bettiCmp, _hgeo⟩ := hgeo
  have hB := GeometricComparisonAdapter.CM.ExtremeSlopes.complex_finite_of_comparisons A (jComplex.comp κ) localCmp bettiCmp
  refine ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, ?_⟩
  intro χ hχ σ
  obtain ⟨L, φS, hφS, hWAS, hcompS, hweights, hdata⟩ := hsumm χ hχ σ
  have hn := GeometricComparisonAdapter.CM.ExtremeSlopes.summand_comparison_numbers A (jComplex.comp κ) H ρ P
    (fun h => ι (σ (χ h))) (fun h => jComplex (σ (χ h)))
    L Fil hFil φS hWAS hcompS
  refine ⟨L, φS, hφS, hWAS, hweights, hdata,
    Filtration.CM.ExtremeSlopesAdapter.coefficient_weaklyAdmissible01 q L.field Fil _ φS hWAS hn.2.1 hn.2.2.1,
    hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, ?_⟩
  exact intrinsic_newton_eq_hodge_of_comparison q L.field
    (V := A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L) φS _ hn.2.2.2.2

end CM.Adapter

end NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

namespace NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter

/-!
Terminal purity implication using the verified intrinsic Newton formula.
`hdata`, `hDim`, and `hcomparison` are returned on the SAME genuine summand by
`verified_native_summands_of_full_GeometricComparison`. The sign inputs are the conclusions
of `signs_of_full_GaloisValuation`. The remaining graph and actual projector/graded-action
identifications are explicit; none is replaced by a Hodge-purity assumption.
-/

open scoped TensorProduct

/-- Combine verified NewtonData, GeometricComparison's normalized Hodge comparison, and
GaloisValuation's sign rule, retaining all residual arithmetic and projector inputs. -/
theorem pure_type_from_verified_newton_data
    (q : ℕ) [Fact q.Prime]
    {K U : Type*} [Field K] [CharZero K]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U]
    (jC : K →+* ℂ) (ι : K →+* AlgebraicClosure ℚ_[q]) (f : U ≃ₗ[L] U)
    (hdata : FrobeniusSlopeComparisonNewton.NewtonData (L := L) (U := U) q jC ι f)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (hCubicRelation :
      (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 3 - T 0 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q]))) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hCommuting : FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ)) (hνq : ν (q : (AlgebraicClosure ℚ_[q])) = 1)
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ))
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B S : Submodule ℂ W) (h_HodgeDecomposition : IsCompl A B)
    (P : Module.End ℂ W) (hRange : LinearMap.range P = S)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B)
    (hne : S ≠ ⊥)
    (hDim : Module.finrank L U = Module.finrank ℂ S)
    (hcomparison : FrobeniusSlopeComparisonNewton.newton q L U f =
      (Module.finrank ℂ ↥(S ⊓ A) : ℚ))
    (sign : Bool) (initial : ℚ)
    (hGaloisValuation_initial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hGaloisValuation_sign : Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial) :
    let slope : ℚ := 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧
    (slope = 1 ↔ S ≤ A) ∧ (slope = 0 ↔ S ≤ B) := by
  have hn := intrinsic_newton_with_GaloisValuation_valuation q L jC ι f hdata
    r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm
    hCubicRelation hCentralConstraint_satake hCommuting ν hνq s hνe
  rw [hGaloisValuation_sign, hDim] at hn
  have hnumber := hcomparison.symm.trans hn
  have hext := IntrinsicPurity.CM.ExtremeSlopesAdapter.extreme_slope_of_sign sign initial (Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e))
    hGaloisValuation_initial hGaloisValuation_sign
  rw [hGaloisValuation_sign] at hext
  refine ⟨hext, ?_⟩
  have hp := ExtremeSlopes.CM.Construction.pure_type_of_extreme_number A B h_HodgeDecomposition P hA hB
    (by rwa [hRange]) _ hext (by rwa [hRange])
  simpa only [hRange] using hp

/-- The residual arithmetic, grading and projector hypotheses needed on one
specified summand. This is a conclusion of the combined adapter, never an input. -/
def ConditionalPurity
    (q : ℕ) [Fact q.Prime]
    {K U : Type*} [Field K] [CharZero K]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U]
    (jC : K →+* ℂ) (ι : K →+* AlgebraicClosure ℚ_[q]) (f : U ≃ₗ[L] U)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A S : Submodule ℂ W) : Prop := ∀
    (r b e : K) (_hr : r ^ 2 = (q : K))
    (_hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (_hC4_10 : ‖jC e‖ = 1)
    (_hL4_18_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (_hcomm : ∀ i j, Commute (T i) (T j))
    (_hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (_hP4_14 :
      (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 3 - T 0 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q]))) - (q ^ 3) • T 2 = 0)
    (_hL4_18_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (_hE67 : FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ)) (_hνq : ν (q : (AlgebraicClosure ℚ_[q])) = 1)
    (s : ℚ) (_hνe : ν (ι e) = (s : WithTop ℚ))
    (B : Submodule ℂ W) (_h_E20 : IsCompl A B)
    (P : Module.End ℂ W) (_hRange : LinearMap.range P = S)
    (_hA : ∀ x ∈ A, P x ∈ A) (_hB : ∀ x ∈ B, P x ∈ B)
    (_hne : S ≠ ⊥)
    (sign : Bool) (initial : ℚ)
    (_hL4_12_initial : initial = -3 / 2 ∨ initial = 3 / 2)
    (_hL4_12_sign : Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial),
    let slope : ℚ := 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧
    (slope = 1 ↔ S ≤ A) ∧ (slope = 0 ↔ S ≤ B)

/-- Derive the whole residual implication from the three pieces of numerical
data carried by a single comparison witness. -/
theorem conditional_purity_of_verified_newton_data
    (q : ℕ) [Fact q.Prime]
    {K U : Type*} [Field K] [CharZero K]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U]
    (jC : K →+* ℂ) (ι : K →+* AlgebraicClosure ℚ_[q]) (f : U ≃ₗ[L] U)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A S : Submodule ℂ W)
    (hdata : FrobeniusSlopeComparisonNewton.NewtonData (L := L) (U := U) q jC ι f)
    (hDim : Module.finrank L U = Module.finrank ℂ S)
    (hcomparison : FrobeniusSlopeComparisonNewton.newton q L U f =
      (Module.finrank ℂ ↥(S ⊓ A) : ℚ)) :
    ConditionalPurity q L jC ι f A S := by
  intro r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm hCubicRelation hCentralConstraint_satake
    hCommuting ν hνq s hνe B h_HodgeDecomposition P hRange hA hB hne sign initial hInitial hSign
  exact pure_type_from_verified_newton_data q L jC ι f hdata
    r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm hCubicRelation hCentralConstraint_satake
    hCommuting ν hνq s hνe A B S h_HodgeDecomposition P hRange hA hB hne hDim hcomparison
    sign initial hInitial hSign

end NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter

namespace NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

/-!
# Coherent GeometricComparison → FrobeniusSlope → ExtremeSlopes adapter

Choose the full GeometricComparison comparison once through the verified FrobeniusSlope adapter.
For each occurring character and each conjugate, choose its finite coefficient
field and restricted Frobenius once. Numerical weak admissibility, intrinsic
Newton/Hodge equality and the conditional purity implication all use that
same field, summand and Frobenius. No equality of existentially selected
witnesses is postulated.
-/

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

namespace CM.Adapter

variable {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

/-- The actual GeometricComparison summands, all their numerical comparison data, and the
purity implication using those same witnesses. -/
def VerifiedNativePurityComparison
    [FiniteDimensional ℚ_[q] A.DeRham]
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    [FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ))]
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
          FrobeniusSlopeComparisonNewton.NewtonData (L := L.field) (U := S) q jComplex ι φS ∧
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
                A.bettiFiltration (jComplex.comp κ) P 1) : ℚ) ∧
          FrobeniusSlopeComparisonNewton.newton q L.field S φS =
            (Module.finrank ℂ ↥(B ⊓ A.bettiFiltration (jComplex.comp κ) P 1) : ℚ) ∧
          ConditionalPurity q (U := S) (W := A.ComplexBetti (jComplex.comp κ))
            L.field jComplex ι φS
            (A.bettiFiltration (jComplex.comp κ) P 1) B

/-- Specialize the numerical purity result to one actual geometric summand,
keeping the geometric comparison embedding as a named parameter. -/
theorem conditional_purity_on_native_summand
    [FiniteDimensional ℚ_[q] A.DeRham]
    (j : K →+* ℂ) [FiniteDimensional ℂ (A.ComplexBetti j)]
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (χq : H → AlgebraicClosure ℚ_[q]) (χc : H → ℂ)
    (L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq) :
    let S := A.deRhamHeckeSummand ρ χq L
    let B := A.bettiHeckeSummand j ρ χc
    ∀ (f : S ≃ₗ[L.field] S),
      FrobeniusSlopeComparisonNewton.NewtonData (L := L.field) (U := S) q jComplex ι f →
      Module.finrank L.field S = Module.finrank ℂ B →
      FrobeniusSlopeComparisonNewton.newton q L.field S f =
        (Module.finrank ℂ ↥(B ⊓ A.bettiFiltration j P 1) : ℚ) →
      ConditionalPurity q (U := S) (W := A.ComplexBetti j) L.field jComplex ι f
        (A.bettiFiltration j P 1) B := by
  intro S B f hdata hdim hnewton
  let : AddCommGroup S := inferInstance
  let : Module L.field S := inferInstance
  let : Module ℚ_[q] S := inferInstance
  let : Module.Free L.field S := inferInstance
  let : AddCommGroup (A.ComplexBetti j) := inferInstance
  let : Module ℂ (A.ComplexBetti j) := inferInstance
  exact conditional_purity_of_verified_newton_data q
    (U := S) (W := A.ComplexBetti j) L.field jComplex ι f _ _ hdata hdim hnewton

/-- Add the purity implication to each already chosen comparison summand. -/
theorem verified_native_purity_comparison
    [FiniteDimensional ℚ_[q] A.DeRham]
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    [FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ))]
    (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (hsumm : VerifiedNativeSummandComparison A κ jComplex ι H ρ P Fil φdR) :
    VerifiedNativePurityComparison A κ jComplex ι H ρ P Fil φdR := by
  intro χ hχ σ
  obtain ⟨L, φS, hincl, hWA, hweight, hdata, hWA01, hdim, h0, h2, h1, hraw, hnewton⟩ :=
    hsumm χ hχ σ
  refine ⟨L, φS, hincl, hWA, hweight, hdata, hWA01, hdim, h0, h2, h1, hraw, hnewton, ?_⟩
  exact conditional_purity_on_native_summand A (jComplex.comp κ) jComplex ι H ρ P
    (fun h => ι (σ (χ h))) (fun h => jComplex (σ (χ h))) L φS hdata hdim hnewton

/-- Full-input combined interface for the geometric application. Every residual
parameter, grading and projector hypothesis is exposed in `ConditionalPurity`
on the returned actual summand. -/
theorem coherent_purity_adapter_of_full_GeometricComparison
    (h_GeometricComparison : GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
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
        VerifiedNativePurityComparison A κ jComplex ι H ρ P Fil
          (cmp.symm.trans (φ.trans cmp)) := by
  obtain ⟨_hfull, hD, hC, hB, cmp, φ, Fil, hφ, hFil, hsumm⟩ :=
    verified_native_summands_of_full_GeometricComparison A h_GeometricComparison κ jComplex ι hplace H ρ P ℓ hℓq
  let := hD
  let := hC
  let := hB
  refine ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, ?_⟩
  exact verified_native_purity_comparison A κ jComplex ι H ρ P Fil _ hsumm

end CM.Adapter

end NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

end

end OAI
