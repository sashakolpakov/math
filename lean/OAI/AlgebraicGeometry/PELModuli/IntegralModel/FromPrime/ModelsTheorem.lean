import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsAlbaneseData
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentAlbaneseConsequences
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone

/-! # Models Theorem -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsTheorem.FromPrimeModels

noncomputable section

/-! The full IntegralModel conclusion from actual arithmetic prime-level models
for the fixed PEL datum, ReferenceFamily, and the endomorphism-equation theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem projective_models_and_albanese_generation
    (h43 : ReferenceFamily.ModuliInput)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E K : Type}
    [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ)
    (h_embedding : κ.comp iota = P.μ)
    (N : ℕ) (hN : PEL.Has.IsSufficientlyDeepFullLevel P N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
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
  obtain ⟨B, hNB, T, hT, hsm, hp, hproj, r, D, e, hD⟩ :=
    ModelsAlbaneseData.FromPrimeModels.exists_complete_arithmetic_pel_albanese_data h43 hPresentations
      s hs hdegree P hP iota κ h_embedding N hN.1 M hM
  have hS : ∀ j, Smooth (D.S j).hom ∧ IsProper (D.S j).hom ∧
      Components.RelativelyProjective (D.S j) ∧ GeometricallyConnected (D.S j).hom :=
    fun j => ⟨(hD j).1, (hD j).2.1, (hD j).2.2.1, (hD j).2.2.2.1⟩
  have hA : ∀ j, Smooth (D.A j).X.hom ∧ IsProper (D.A j).X.hom ∧ GeometricallyConnected (D.A j).X.hom :=
    fun j => ⟨(hD j).2.2.2.2.1, (hD j).2.2.2.2.2.1, (hD j).2.2.2.2.2.2.1⟩
  have hAlb : ∀ j, D.IsComplexAlbanese B.complexPoint j := fun j => (hD j).2.2.2.2.2.2.2
  have : IsDominant B.complexPoint := B.complexPoint_dominant
  exact ⟨B, hNB, T, hT, hsm, hp, hproj, r, D, e, hD,
    D.total_h1_of_component_geometry HodgeComparisonCapstone.provedHodgeComparisonInput B.complexPoint e hS hA hAlb,
    D.generation_of_component_geometry B.complexPoint hS hA hAlb⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsTheorem.FromPrimeModels
