import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.ConcentrationTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace

/-! # Unit Pure Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass

noncomputable section

/-! The original unit class has trace one after passing to its pure
cohomology degree. This applies equally to finite coefficient sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace (cohomology)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (f : M ⟶ N)
  (eM : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)
  (eN : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology N 0)
  (hf : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map f (eM 1) = eN 1)
  (c : ℕ)
  (hPure : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)
  (i : ℕ) (hi : i + c = n + 1)

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre.fixedTower M B n hn
local notation "hT" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre.fixed_above M B n hn

def concentration := ProjectiveTower.ConcentrationTrace.concentration T B n hn hT hB c hPure i hi

def pureClass := (concentration M B n hn hB c hPure i hi).hom
  (TotalUnitMap.unitClass M N B n hn hB f eM eN)

include hf in
theorem trace_one :
    PureTrace.trace M B n hn hB c hPure i hi (eM 1)
      (pureClass M N B n hn hB f eM eN c hPure i hi) = 1 := by
  let x := TotalUnitMap.unitClass M N B n hn hB f eM eN
  have hc := ConcreteCategory.congr_hom
    (ProjectiveTower.ConcentrationTrace.trace T B n hn hT hB c hPure i hi (eM 1)) x
  have ht : (TotalUnitMap.fixedTrace M B n hn hB eM).hom x = 1 :=
    TotalUnitMap.unitClass_trace M N B n hn hB f eM eN hf
  rw [TotalUnitMap.fixedTrace, ProjectiveTower.TotalTrace.traceIso_hom] at ht
  exact hc.trans ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass
