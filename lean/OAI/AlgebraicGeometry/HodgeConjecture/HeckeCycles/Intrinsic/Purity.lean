import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators
import OAI.NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands

/-! # Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Purity.CM

noncomputable section

/-! Discharge the operator premises of the verified ExtremeSlopes purity
implication on its actual GeometricComparison summand. Only the arithmetic character
values, valuations, and Hodge projector data remain to be supplied. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (hcomm : ∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k))
  (χ : H → AlgebraicClosure ℚ_[q]) (L : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteHeckeCoefficientField q χ)

local instance : AddCommGroup (A.deRhamHeckeSummand ρ χ L) :=
  (A.deRhamHeckeSummand ρ χ L).addCommGroup
local instance : Module L.field (A.deRhamHeckeSummand ρ χ L) :=
  (A.deRhamHeckeSummand ρ χ L).module

include hcomm

theorem purity_from_native_operators
    (f : Module.End ℚ_[q] A.DeRham)
    (fS : (A.deRhamHeckeSummand ρ χ L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χ L))
    (hincl : ∀ x : A.deRhamHeckeSummand ρ χ L,
      (fS x : L.field ⊗[ℚ_[q]] A.DeRham) = NumberTheory.PadicHodge.GeometricComparison.Linear.coefficientFrobenius L.field f
        (x : L.field ⊗[ℚ_[q]] A.DeRham))
    (hfcomm : ∀ h, Commute f (A.deRhamHecke ρ h))
    (idx : Fin 3 → H) (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f (fun i => A.deRhamHecke ρ (idx i)) = 0)
    {C W : Type*} [Field C] [CharZero C]
    (jC : C →+* ℂ) (iota : C →+* AlgebraicClosure ℚ_[q])
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (hol anti S : Submodule ℂ W)
    (hpurity : NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.ConditionalPurity q (U := A.deRhamHeckeSummand ρ χ L)
      L.field jC iota fS hol S)
    (r b e : C) (hr : r ^ 2 = (q : C))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (heC : ‖jC e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i : Fin 3,
      χ (idx i) = iota ((![(q : C) * b * (r + r⁻¹ + e),
        (q : C) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e), b ^ 3 * e] : Fin 3 → C) i))
    (hCommuting : NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q])
      ((AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L)))
    (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ))
    (hνq : ν (q : AlgebraicClosure ℚ_[q]) = 1)
    (s : ℚ) (hνe : ν (iota e) = (s : WithTop ℚ))
    (hcompl : IsCompl hol anti)
    (P : Module.End ℂ W) (hRange : LinearMap.range P = S)
    (hhol : ∀ x ∈ hol, P x ∈ hol) (hanti : ∀ x ∈ anti, P x ∈ anti)
    (hne : S ≠ ⊥) (sign : Bool) (initial : ℚ)
    (hinitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hsign : NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (iota e) = (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial) :
    let slope : ℚ := 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧ (slope = 1 ↔ S ≤ hol) ∧ (slope = 0 ↔ S ≤ anti) := by
  obtain ⟨hTcomm, hFTcomm, hpoly, heigen⟩ :=
    SummandOperators.CM.operators_on_native_summand A ρ hcomm χ L f fS hincl hfcomm idx hp
  apply hpurity r b e hr hrC heC hcentral
    (fun i => SummandOperators.CM.closureHecke A ρ hcomm χ L (idx i)) hTcomm hFTcomm hpoly
    _ hCommuting ν hνq s hνe anti hcompl P hRange hhol hanti hne sign initial hinitial hsign
  intro i
  rw [← hvalues i]
  exact heigen i

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Purity.CM
