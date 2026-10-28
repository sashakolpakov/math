import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticSpread
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentAlbaneseExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.SpreadBaseChange
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Models Albanese Data -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsAlbaneseData

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FromPrimeModels

theorem exists_complete_arithmetic_pel_albanese_data
    (h43 : ReferenceFamily.ModuliInput)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ T : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B,
        T.IsReducedPELModuli P ∧ Smooth T.toOver.hom ∧ IsProper T.toOver.hom ∧
          Components.RelativelyProjective T.toOver ∧
          ∃ (r : ℕ) (D : Components.ComponentAlbaneseData T.toOver r) (_e : (∐ D.S) ≅ T.toOver),
            ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ Components.RelativelyProjective (D.S i) ∧
              GeometricallyConnected (D.S i).hom ∧ Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧
              GeometricallyConnected (D.A i).X.hom ∧ D.IsComplexAlbanese B.complexPoint i := by
  obtain ⟨B, hNB, T, hT, hsm, hp, hproj⟩ := ModelsArithmeticSpread.FromPrimeModels.exists_smooth_projective_arithmetic_pel_spread
    h43 hPresentations s hs hdegree P hP iota κ hemb N hN M hM
  have : Smooth T.toOver.hom := hsm
  have : IsProper T.toOver.hom := hp
  obtain ⟨L, φ, hφ, r, D, e, hD⟩ := Arithmetic.ComponentAlbaneseExistence.arithmetic_component_albanese_exists B T.toOver hproj
  let C := B.compose L
  let g := Spec.map (CommRingCat.ofHom φ)
  let Q := (Over.pullback g).obj T.toOver
  have hsmQ : Smooth Q.hom := inferInstanceAs (Smooth (pullback.snd T.toOver.hom g))
  have hpQ : IsProper Q.hom := inferInstanceAs (IsProper (pullback.snd T.toOver.hom g))
  have : IsReduced Q.left :=
    ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.smooth_model_reduced_of_injective_generic C.toField C.toField_injective Q
  let V := T.baseChangeFine L φ hφ hT hM
  have hNC : IsUnit (N : C.R) := by simpa only [map_natCast] using hNB.map φ
  exact ⟨C, hNC, V, T.baseChangeFine_isReducedPELModuli L φ hφ hT hM,
    hsmQ, hpQ, ComponentBaseChange.relativelyProjective_baseChange g hproj, r, D, e, hD⟩

end FromPrimeModels

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsAlbaneseData
