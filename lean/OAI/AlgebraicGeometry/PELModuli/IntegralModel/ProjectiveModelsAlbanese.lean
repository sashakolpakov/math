import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteArithmeticPrimeModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamilyConstructed
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsTheorem

/-! # Projective Models Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese

noncomputable section

/-! IntegralModel from the constructed arithmetic prime models and the proved
ReferenceFamily and endomorphism-equation theorems. No abstract moduli input remains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem projective_models_and_albanese_generation_unconditional
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
  let : Arithmetic.PrimeModels.ArithmeticPrimePELModels P := ConcreteArithmeticPrimeModels.actualArithmeticPrimePELModels P hP hs
  exact FromPrime.ModelsTheorem.FromPrimeModels.projective_models_and_albanese_generation
    ReferenceFamilyConstructed.provedReferenceFamilyModuliInput Alternative.AlternativeStrategies.provedEndomorphismEquationsInput
    s hs hdegree P hP iota κ h_embedding N hN M hM

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProjectiveModelsAlbanese
