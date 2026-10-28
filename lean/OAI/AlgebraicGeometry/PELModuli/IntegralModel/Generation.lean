import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Definitions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese

/-! # Generation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Generation

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese

/-! The IntegralModel statement, with its proof supplied by the completed development. -/

/-- IntegralModel: projective integral PEL models, Albanese H¹ comparison, and uniform
surjectivity of finite sums of point differences on every geometric fiber. -/
theorem projective_models_and_albanese_generation
    {E K : Type}
    [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ)
    (h_embedding : κ.comp iota = P.μ)
    (N : ℕ) (hN : PEL.Has.IsSufficientlyDeepFullLevel P N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (hM : M.IsFine) :
    ∃ B : Base.ArithmeticBaseExtension K κ,
      IsUnit (N : B.R) ∧
      ∃ T : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B,
        PEL.Has.IntegralPELSpread.IsReducedPELModuli P T ∧
        Smooth T.toOver.hom ∧
        IsProper T.toOver.hom ∧
        Components.RelativelyProjective T.toOver ∧
        ∃ (r : ℕ) (D : Components.ComponentAlbaneseData T.toOver r)
          (e : (∐ D.S) ≅ T.toOver),
          (∀ j : Fin r,
            Smooth (D.S j).hom ∧
            IsProper (D.S j).hom ∧
            Components.RelativelyProjective (D.S j) ∧
            GeometricallyConnected (D.S j).hom ∧
            Smooth (D.A j).X.hom ∧
            IsProper (D.A j).X.hom ∧
            GeometricallyConnected (D.A j).X.hom ∧
            D.IsComplexAlbanese B.complexPoint j) ∧
          Function.Bijective
            (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
              (D.totalComplexMap B.complexPoint e)).hom ∧
          (∀ j : Fin r, ∃ n : ℕ, 0 < n ∧
            ∀ t : Base.GeometricPoint B.base,
              Function.Surjective (D.sumOfDifferences j n t)) := by
  exact ProjectiveModelsAlbanese.projective_models_and_albanese_generation_unconditional
    s hs hdegree P hP iota κ h_embedding N hN M hM

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Generation
