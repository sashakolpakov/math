import OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport

/-! # Abstract Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.AbstractRealization

noncomputable section

/-! The embedded-field RiemannProjectivity statement realizes all three constructed
types for the abstract coefficient field in the CMPoints specification. -/

open scoped Classical

open _root_.NumberField _root_.Algebra

theorem cmField_of_fieldEquiv {E F : Type} [Field E] [NumberField E] [IsCMField E]
    [Field F] [NumberField F] (e : E ≃+* F) : IsCMField F := by
  let : IsTotallyComplex F := ⟨fun w =>
    InfinitePlace.IsComplex.of_comap e.toRingHom (IsTotallyComplex.isComplex _)⟩
  let : Algebra (maximalRealSubfield E) F := (e.toRingHom.comp (algebraMap (maximalRealSubfield E) E)).toAlgebra
  let : IsQuadraticExtension (maximalRealSubfield E) F := ⟨by
    calc
      Module.finrank (maximalRealSubfield E) F = Module.finrank (maximalRealSubfield E) E :=
        Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (maximalRealSubfield E)) e.symm (by
          ext x
          change (x : E) = e.symm (e (x : E))
          exact (e.symm_apply_apply _).symm)
      _ = 2 := IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield E) F

theorem exists_abstract_CM_realization (hRiemannProjectivity : Realization.RiemannProjectivityInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E] [IsCMField E]
    (σ : E →ₐ[ℚ] ℂ) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization ε.hodgeStructure, R.abelianVariety.HasCMH1 := by
  let F : IntermediateField ℚ ℂ := σ.fieldRange
  let e : E ≃ₐ[ℚ] F := σ.equivFieldRange
  let : NumberField F := NumberField.of_ringEquiv E F e.toRingEquiv
  let : IsCMField F := cmField_of_fieldEquiv e.toRingEquiv
  let : IsGalois ℚ F := IsGalois.of_algEquiv e
  obtain ⟨R, hR⟩ := PeriodCoordinates.exists_CM_realization_of_embeddingType F hRiemannProjectivity (TypeTransport.cmTypeAlongEquiv e ε)
  exact ⟨TypeTransport.cmRealizationAlongEquiv e ε R, hR⟩

theorem exists_abstract_coordinate_CM_realizations (hRiemannProjectivity : Realization.RiemannProjectivityInput) (hCMAbelianVariety : Descent.AbelianInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E] [IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) :
    ∃ R : ∀ j : Fin 3, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (PeriodCoordinates.coordinateCMType P hP j).hodgeStructure,
      ∀ j, (R j).abelianVariety.HasCMH1 ∧ ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel (R j).abelianVariety := by
  have hex (j : Fin 3) := exists_abstract_CM_realization hRiemannProjectivity
    (P.embeddings P.distinguished) (PeriodCoordinates.coordinateCMType P hP j)
  choose R hR using hex
  exact ⟨R, fun j => ⟨hR j, hCMAbelianVariety (R j).abelianVariety (hR j)⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.AbstractRealization
