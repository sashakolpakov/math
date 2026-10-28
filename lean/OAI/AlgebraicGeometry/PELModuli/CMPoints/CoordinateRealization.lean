import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Iso

/-! # Coordinate Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateRealization

noncomputable section

/-! Coordinate CM realizations and their transport through actual
scheme isomorphisms, independent of the component-existence proof. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.Module
open scoped Classical

def coordinateRealizationOfBasisPeriod
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E)) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (hH : ∀ x, x ∈ H.holomorphic ↔ x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization (PeriodCoordinates.coordinateCMHodge P hP) := by
  have hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (BasisHodge.basisCMHodge P hP b) H LinearMap.id := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using (hH x).mpr hx
  have hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap H (BasisHodge.basisCMHodge P hP b) LinearMap.id := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using (hH x).mp hx
  exact TypeTransport.hodgeRealizationAlongEquiv (BasisHodge.rationalBasisEquiv b)
    ((PeriodCoordinates.coordinateCMHodge P hP).transport_isHodgeMap _)
    ((PeriodCoordinates.coordinateCMHodge P hP).transport_symm_isHodgeMap _)
    (TypeTransport.hodgeRealizationAlongEquiv (LinearEquiv.refl ℚ _) hf hi R)

def HasCoordinateCMRealization
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Prop :=
  ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (PeriodCoordinates.coordinateCMHodge P hP), R.abelianVariety = A

theorem HasCoordinateCMRealization.hasCMH1
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible} {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (h : HasCoordinateCMRealization P hP A) : A.HasCMH1 := by
  obtain ⟨R, rfl⟩ := h
  exact PeriodCoordinates.coordinateCMRealization_hasCMH1 P hP R

def hodgeRealizationOfSchemeIso
    {U : Type*} [AddCommGroup U] [Module ℚ U] {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : B.toOver ≅ R.abelianVariety.toOver) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization H where
  abelianVariety := B
  comparison := R.comparison.trans (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e 1)
  holomorphic x := by
    rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact (Iso.h1Pullback_iso_holomorphic e _).trans (R.holomorphic x)
  antiholomorphic x := by
    rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact (Iso.h1Pullback_iso_antiholomorphic e _).trans (R.antiholomorphic x)

theorem HasCoordinateCMRealization.of_iso
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible} {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (e : B.toOver ≅ A.toOver) (h : HasCoordinateCMRealization P hP A) :
    HasCoordinateCMRealization P hP B := by
  obtain ⟨R, rfl⟩ := h
  exact ⟨hodgeRealizationOfSchemeIso R B e, rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateRealization
