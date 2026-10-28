import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Integral Model -/

namespace OAI.RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic

noncomputable section

/-! The entire committed IntegralModel proposition, with no statement theorem used. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Betti.Scheme

def FullIntegralModelInput : Prop := ∀
    {E K : Type}
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

end

end OAI.RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic
