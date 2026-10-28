import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.Analysis.HodgeTheory.Decomposition.Core
import OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariants
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Good
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.Completion
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.Shared
import OAI.NumberTheory.PadicHodge.GeometricComparison.Betti

/-! # Graph Prerequisite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.GraphPrerequisite

noncomputable section

/-! The complete named graph prerequisites for the conditional GeometricComparison entry
point. These propositions reproduce the committed statements on their
geometric objects. Their theorem declarations are not imported. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- The full IntegralModel integral-model, Albanese-comparison and generation assertion. -/
def GeometricInput : Prop :=
  ∀ {E K : Type}
    [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (_hs : 0 < s)
    (_hdegree : Module.finrank ℚ E = 2 * s)
    (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (_hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ)
    (_h_embedding : κ.comp iota = P.μ)
    (N : ℕ) (_hN : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (_hM : M.IsFine),
    ∃ B : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ,
      IsUnit (N : B.R) ∧
      ∃ T : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B,
        AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.IsReducedPELModuli P T ∧
        Smooth T.toOver.hom ∧
        IsProper T.toOver.hom ∧
        AlgebraicGeometry.PELModuli.IntegralModel.Components.RelativelyProjective T.toOver ∧
        ∃ (r : ℕ) (D : AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData T.toOver r)
          (e : (∐ D.S) ≅ T.toOver),
          (∀ j : Fin r,
            Smooth (D.S j).hom ∧
            IsProper (D.S j).hom ∧
            AlgebraicGeometry.PELModuli.IntegralModel.Components.RelativelyProjective (D.S j) ∧
            GeometricallyConnected (D.S j).hom ∧
            Smooth (D.A j).X.hom ∧
            IsProper (D.A j).X.hom ∧
            GeometricallyConnected (D.A j).X.hom ∧
            D.IsComplexAlbanese B.complexPoint j) ∧
          Function.Bijective
            (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
              (D.totalComplexMap B.complexPoint e)).hom ∧
          (∀ j : Fin r, ∃ n : ℕ, 0 < n ∧
            ∀ t : AlgebraicGeometry.PELModuli.IntegralModel.Base.GeometricPoint B.base,
              Function.Surjective (D.sumOfDifferences j n t))

/-- The complete TateComparison statement, including its original explicit inputs. -/
abbrev HeckeInput : Prop := AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM.TateComparisonInput

open OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions in
/-- HodgeDecomposition with the independently defined Hodge pieces and closed-form filtration. -/
def HodgeInput : Prop :=
  ∀ (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ),
    DirectSum.IsInternal (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n) ∧
    (∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ]
        X.complexCohomology n,
      Function.Involutive c ∧
      (∀ ω : X.componentClosedForms n,
        c (X.closedFormBettiClass n ω) =
          X.closedFormBettiClass n (Analysis.HodgeTheory.Decomposition.Core.Constructions.conjugateClosed X n ω)) ∧
      (∀ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (x : X.complexCohomology n),
        x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i ↔
          c x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i))) ∧
    (∀ p : ℤ,
      Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti X n p =
        ⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
          Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.GraphPrerequisite
