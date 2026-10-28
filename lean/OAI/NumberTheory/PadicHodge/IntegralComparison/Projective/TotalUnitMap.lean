import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.TotalTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.TotalRefinement

/-! # Total Unit Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitMap

noncomputable section

/-! The unit class transported by the original common negative
resolution. This construction precedes purity and therefore applies to
an actual quotient onto a section of different codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.TotalTrace
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace (cohomology)

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

abbrev fixed := ProjectiveRefinement.Serre.fixedTower M B n hn
abbrev common := NegativeRefinement.tower M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f

def fixedTrace := ProjectiveTower.TotalTrace.traceIso (fixed M B n hn) B n hn
  (ProjectiveRefinement.Serre.fixed_above M B n hn) hB eM

def commonTrace := ProjectiveTower.TotalTrace.traceIso (common M N B n hn f) B n hn
  (NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) hB eM

abbrev left := HomologicalComplex.homologyMap
  (ProjectiveTower.TotalTrace.totalMap n hn (NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)) (n + 1)
abbrev right := HomologicalComplex.homologyMap
  (ProjectiveTower.TotalTrace.totalMap n hn (NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)) (n + 1)

theorem left_trace : left M N B n hn f ≫ (commonTrace M N B n hn hB f eM).hom =
    (fixedTrace M B n hn hB eM).hom := by
  simp only [commonTrace, fixedTrace, ProjectiveTower.TotalTrace.traceIso_hom]
  exact ProjectiveTower.TotalTrace.naturality B n hn
    (NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) hB
    (ProjectiveRefinement.Serre.fixed_above M B n hn)
    (NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)
    (eM 1) (eM 1) (by
      change (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (𝟙 M) (eM 1) = eM 1
      rw [CategoryTheory.Functor.map_id]
      rfl)

include hf in
theorem right_trace : right M N B n hn f ≫ (commonTrace M N B n hn hB f eM).hom =
    (fixedTrace N B n hn hB eN).hom := by
  simp only [commonTrace, fixedTrace, ProjectiveTower.TotalTrace.traceIso_hom]
  exact ProjectiveTower.TotalTrace.naturality B n hn
    (NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) hB
    (ProjectiveRefinement.Serre.fixed_above N B n hn)
    (NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)
    (eM 1) (eN 1) hf

def map := Trace.TotalRefinement.map
  (fixedTrace M B n hn hB eM) (commonTrace M N B n hn hB f eM)
  (left M N B n hn f) (right M N B n hn f) (left_trace M N B n hn hB f eM)

def unitClass := Trace.TotalRefinement.unitClass
  (fixedTrace M B n hn hB eM) (fixedTrace N B n hn hB eN) (commonTrace M N B n hn hB f eM)
  (left M N B n hn f) (right M N B n hn f) (left_trace M N B n hn hB f eM)

include hf in
abbrev unitClass_trace := Trace.TotalRefinement.unitClass_trace
  (fixedTrace M B n hn hB eM) (fixedTrace N B n hn hB eN) (commonTrace M N B n hn hB f eM)
  (left M N B n hn f) (right M N B n hn f) (left_trace M N B n hn hB f eM)
  (right_trace M N B n hn hB f eM eN hf)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitMap
