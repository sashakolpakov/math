import OAI.NumberTheory.PadicHodge.IntrinsicParameters
import OAI.NumberTheory.PadicHodge.GeometricComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators
import OAI.LinearAlgebra.Endomorphisms.Commuting

/-! # Intrinsic Summands -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicSummands

noncomputable section

/-! Resolve the numerical FrobeniusSlope premises on GeometricComparison's actual conjugated
Hecke summands, using the geometric polynomial and character values. -/

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

namespace FrobeniusSlopeIntrinsicComparison

def ForcedSlope (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {U : Type*} [AddCommGroup U] [Module L U]
    [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U] [FiniteDimensional L U]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (r b e : AlgebraicClosure ℚ) (f : U ≃ₗ[L] U) : Prop :=
  ∀ (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ)),
    ν (q : AlgebraicClosure ℚ_[q]) = 1 →
    ∀ t : ℚ, ν (ι e) = (t : WithTop ℚ) →
    Module.End.genEigenspace (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (ι (b * r)) ⊤ = ⊤ ∧
    (∀ μ, Module.End.HasEigenvalue (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) μ →
      μ = ι (b * r) ∧ ν μ = ((1 / 2 - t / 3 : ℚ) : WithTop ℚ)) ∧
    algebraMap L (AlgebraicClosure ℚ_[q]) (LinearMap.det f.toLinearMap) =
      ι (b * r) ^ Module.finrank L U ∧
    FrobeniusSlopeComparisonNewton.newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - FrobeniusSlopeComparisonNewton.parameterValuation q L (ι r) (ι b) (ι e) / 3)

/-- The numerical application is independent of geometric type unfolding. -/
theorem forcedSlope_of_newtonData
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {U : Type*} [AddCommGroup U] [Module L U] [Module ℚ_[q] U]
    [IsScalarTower ℚ_[q] L U] [FiniteDimensional L U]
    (j : AlgebraicClosure ℚ →+* ℂ) (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (f : U ≃ₗ[L] U) (hdata : FrobeniusSlopeComparisonNewton.NewtonData (L := L) (U := U) q j ι f)
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : j r = (Real.sqrt (q : ℝ) : ℂ)) (heC : ‖j e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (hT : ∀ i j, Commute (T i) (T j))
    (hFT : ∀ i, Commute (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (hpoly : AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) T = 0)
    (hsat : ∀ i, (T i).genEigenspace (ι (IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i)) ⊤ = ⊤) :
    ForcedSlope (U := U) q L ι r b e f := by
  have h67 : FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q])
      ((AlgebraicClosure ℚ_[q]) ⊗[L] U) := by
    intro V hV
    exact LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure V hV
  intro ν hν t he
  have hout := hdata r b e hr hrC heC hcentral T hT hFT hpoly hsat h67 ν hν t he
  exact ⟨hout.1, hout.2.1, hout.2.2.1,
    FrobeniusSlopeComparisonNewton.intrinsic_newton_on_coefficient_field (U := U) q L j ι f hdata
      r b e hr hrC heC hcentral T hT hFT hpoly hsat h67 ν hν t he⟩

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)

def SummandForced [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
    let χc : H → ℂ := fun h => j (σ (χ h))
    ∃ L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq,
      let S := A.deRhamHeckeSummand ρ χq L
      let B := A.bettiHeckeSummand (j.comp κ) ρ χc
      letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
      ∃ φS : S ≃ₗ[L.field] S,
        (∀ x : S, (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
          GeometricComparison.Linear.coefficientFrobenius L.field φdR.toLinearMap (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
        GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L.field Fil S)
          (φS.restrictScalars ℚ_[q]) ∧
        (∀ i : ℤ,
          Module.finrank L.field (S ⊓ GeometricComparison.Linear.coefficientFiltration L.field A.Fil i :
            Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
          Module.finrank ℂ (B ⊓ A.bettiFiltration (j.comp κ) P i :
            Submodule ℂ (A.ComplexBetti (j.comp κ)))) ∧
        ForcedSlope (U := S) q L.field ι (σ r) (σ b) (σ e) φS

/-- GeometricComparison's integral polynomial gives numerical weight data for the
actual subspace in any complex test embedding. -/
theorem newtonData_on_native_subspace
    [FiniteDimensional ℚ_[q] A.DeRham]
    (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (W : Polynomial ℤ)
    (hchar : LinearMap.charpoly φdR.toLinearMap = W.map (Int.castRingHom ℚ_[q]))
    (hweight : ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ))
    (χq : H → AlgebraicClosure ℚ_[q]) (L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq)
    (φS : (A.deRhamHeckeSummand ρ χq L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χq L))
    (hincl : ∀ x : A.deRhamHeckeSummand ρ χq L,
      (φS x : L.field ⊗[ℚ_[q]] A.DeRham) = GeometricComparison.Linear.coefficientFrobenius L.field φdR.toLinearMap
        (x : L.field ⊗[ℚ_[q]] A.DeRham)) :
    FrobeniusSlopeComparisonNewton.NewtonData (L := L.field) (U := A.deRhamHeckeSummand ρ χq L) q j ι φS := by
  apply FrobeniusSlopeComparisonNewton.newtonData_of_weights (L := L.field) (U := A.deRhamHeckeSummand ρ χq L)
    q (Fact.out : q.Prime) j ι φS
  intro a ha
  exact FrobeniusSlopeComparisonNewton.weights_on_baseChanged_subspace φdR.toLinearMap W hchar q hweight
    (A.deRhamHeckeSummand ρ χq L) φS.toLinearMap hincl j ι a ha

/-- The polynomial and scalar conditions are derived on one actual
coefficient summand, before applying the numerical calculation. -/
theorem forcedSlope_on_native_subspace
    [FiniteDimensional ℚ_[q] A.DeRham]
    (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (W : Polynomial ℤ)
    (hchar : LinearMap.charpoly φdR.toLinearMap = W.map (Int.castRingHom ℚ_[q]))
    (hweight : ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ))
    (hcomm : ∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k))
    (hfcomm : ∀ h, Commute φdR.toLinearMap (A.deRhamHecke ρ h))
    (idx : Fin 3 → H)
    (hp : AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q φdR.toLinearMap
      (fun i => A.deRhamHecke ρ (idx i)) = 0)
    (χq : H → AlgebraicClosure ℚ_[q]) (L : GeometricComparison.Linear.FiniteHeckeCoefficientField q χq)
    (φS : (A.deRhamHeckeSummand ρ χq L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χq L))
    (hincl : ∀ x : A.deRhamHeckeSummand ρ χq L,
      (φS x : L.field ⊗[ℚ_[q]] A.DeRham) = GeometricComparison.Linear.coefficientFrobenius L.field φdR.toLinearMap
        (x : L.field ⊗[ℚ_[q]] A.DeRham))
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : j r = (Real.sqrt (q : ℝ) : ℂ)) (heC : ‖j e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i, χq (idx i) = ι (IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i)) :
    ForcedSlope (U := A.deRhamHeckeSummand ρ χq L) q L.field ι r b e φS := by
  let S := A.deRhamHeckeSummand ρ χq L
  let T := fun i => AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM.closureHecke A ρ hcomm χq L (idx i)
  obtain ⟨hT, hFT, hpoly, hscalar⟩ := AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM.operators_on_native_summand A ρ hcomm
    χq L φdR.toLinearMap φS hincl hfcomm idx hp
  have hsat : ∀ i, (T i).genEigenspace (ι (IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i)) ⊤ = ⊤ := by
    intro i
    simpa only [hvalues] using hscalar i
  have hdata := newtonData_on_native_subspace A j ι ρ φdR W hchar hweight χq L φS hincl
  -- Elaborate forward to avoid unfolding the geometric space during backward unification.
  have numerical := forcedSlope_of_newtonData (U := S) q L.field j ι φS
  have parameters := numerical hdata r b e hr hrC heC hcentral
  have result := parameters T hT hFT hpoly hsat
  exact result

/-- Every conjugate is tested through `j ∘ σ⁻¹`, so its square root has the
required positive complex value. The geometric comparison stays fixed. -/
theorem forced_on_same_summands
    [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (hsumm : GeometricComparison.HeckeScalar.SummandComparison q κ j ι jq A H ρ P Fil φdR)
    (W : Polynomial ℤ)
    (hchar : LinearMap.charpoly φdR.toLinearMap = W.map (Int.castRingHom ℚ_[q]))
    (hweight : ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ))
    (hcomm : ∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k))
    (hfcomm : ∀ h, Commute φdR.toLinearMap (A.deRhamHecke ρ h))
    (idx : Fin 3 → H)
    (hp : AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q φdR.toLinearMap
      (fun i => A.deRhamHecke ρ (idx i)) = 0)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (χ h)) ≠ ⊥)
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : j r = (Real.sqrt (q : ℝ) : ℂ)) (heC : ‖j e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i) :
    SummandForced A κ j ι ρ P Fil φdR χ r b e := by
  intro σ
  obtain ⟨L, φS, hincl, hWA, hdim⟩ := hsumm χ hχ σ
  refine ⟨L, φS, hincl, hWA, hdim, ?_⟩
  let jσ := j.comp σ.symm.toRingHom
  have hrσ : (σ r) ^ 2 = (q : AlgebraicClosure ℚ) := by
    rw [← map_pow, hr, map_natCast]
  have hrCσ : jσ (σ r) = (Real.sqrt (q : ℝ) : ℂ) := by
    change j (σ.symm (σ r)) = _
    simpa only [σ.symm_apply_apply] using hrC
  have heCσ : ‖jσ (σ e)‖ = 1 := by
    change ‖j (σ.symm (σ e))‖ = 1
    simpa only [σ.symm_apply_apply] using heC
  have hcσ : ∃ n : ℕ, 0 < n ∧ ((σ b) ^ 3 * σ e) ^ n = 1 := by
    obtain ⟨n, hn, hc⟩ := hcentral
    exact ⟨n, hn, by rw [← map_pow, ← map_mul, ← map_pow, hc, map_one]⟩
  have hvaluesσ : ∀ i, ι (σ (χ (idx i))) = ι (IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q (σ r) (σ b) (σ e) i) := by
    intro i
    apply congrArg ι
    rw [hvalues]
    exact IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues_map σ.toRingHom q r b e i
  exact forcedSlope_on_native_subspace A jσ ι ρ φdR W hchar hweight hcomm hfcomm idx hp
    (fun h => ι (σ (χ h))) L φS hincl (σ r) (σ b) (σ e) hrσ hrCσ heCσ hcσ hvaluesσ

end FrobeniusSlopeIntrinsicComparison

end

end OAI.NumberTheory.PadicHodge.IntrinsicSummands
