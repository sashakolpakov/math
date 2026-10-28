import OAI.AlgebraicGeometry.PELModuli.CMPoints.Realization
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent

noncomputable section

/-! Apply precisely the two CMAbelianVariety descent conclusions to the actual CM
realizations constructed from RiemannProjectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- CMAbelianVariety's number-field descent statement, with its actual group-scheme model. -/
def AbelianInput : Prop :=
  ∀ A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety, A.HasCMH1 → ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel A

/-- CMAbelianVariety's special-point statement for the supplied enhanced moduli interface. -/
def ModuliInput : Prop :=
  ∀ (M : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.StandardAbelianModuli) (x : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space),
    (M.abelianAt x).HasCMH1 →
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ xK : Spec (CommRingCat.of K) ⟶ M.space,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ xK = x

/-- RiemannProjectivity and CMAbelianVariety give a number-field model for every odd CM sign type. -/
theorem exists_CM_realization_over_numberField
    (hRiemannProjectivity : Realization.RiemannProjectivityInput) (hCMAbelianVariety : AbelianInput)
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) :
    ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v),
      R.abelianVariety.HasCMH1 ∧ ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel R.abelianVariety := by
  obtain ⟨R, hR⟩ := Realization.exists_CM_realization hRiemannProjectivity E v
  exact ⟨R, hR, hCMAbelianVariety R.abelianVariety hR⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent
