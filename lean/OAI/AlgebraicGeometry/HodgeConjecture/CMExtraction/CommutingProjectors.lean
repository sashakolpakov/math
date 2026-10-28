import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors

/-! # Commuting Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingProjectors.Spectral

noncomputable section

/-! Construct the actual algebraic spectral projectors while retaining
commutation with every rational Hecke operator, together with the full
coefficient-field, Hodge, character, and Galois-conjugation conclusions. -/

open scoped Classical TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.GaloisLift OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.SpectralConjugation
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors.CM

theorem construct_commuting_algebraic_projectors
    (E : IntermediateField ℚ ℂ) [NumberField E]
    {U J Φ : Type*} [AddCommGroup U] [Module ℚ U]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (T : J → Module.End ℚ U)
    (hcomm : ∀ j k, Commute (T j) (T k))
    (hHodge : ∀ j, ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (T j))
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification U) :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧ E ≤ K ∧
      ∃ (hKalg : K ≤ HeckeCycles.Coefficients.CM.algebraicField) (n : ℕ) (p : Fin n → K ⊗[ℚ] (U →ₗ[ℚ] U))
        (χ : Fin n → J → HeckeCycles.Coefficients.CM.algebraicField),
        let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i)
        let A := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U (p i))
        (∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, LinearMap.range (P i) = Definitions.CM.conjugateSpace K (A i) 1) ∧
        (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
        (∀ i j, Commute (P i) ((T j).baseChange ℂ)) ∧
        (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
        (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
        (∀ i, LinearMap.range (P i) = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ)
          (fun j => (χ i j : ℂ))) ∧
        (∀ i (σ : Gal(K/ℚ)),
          let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U
            (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ (p i))
          ∃ τ : Gal(HeckeCycles.Coefficients.CM.algebraicField/ℚ),
            (∀ a : K, (τ (IntermediateField.inclusion hKalg a) : ℂ) =
              (σ a : ℂ)) ∧ Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
            LinearMap.range Pσ = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ)
              (fun j => (τ (χ i j) : ℂ))) := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  let C := HeckeCycles.Coefficients.CM.algebraicField
  let TA : J → Module.End C (C ⊗[ℚ] U) := fun j => (T j).baseChange C
  have hTA : ∀ j k, Commute (TA j) (TA k) := by
    intro j k
    change (T j).baseChange C * (T k).baseChange C =
      (T k).baseChange C * (T j).baseChange C
    simpa only [LinearMap.baseChange_mul] using
      congrArg (fun f : Module.End ℚ U => f.baseChange C) (hcomm j k).eq
  obtain ⟨hfinite, hinternal⟩ := HeckeCycles.HeckeCharacters.CM.Projectors.joint_finite_and_internal TA hTA
  let Spectrum := {χ : J → C // HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace TA χ ≠ ⊥}
  let : Fintype Spectrum := hfinite.fintype
  let χ : Spectrum → J → C := fun i => i.val
  let S : Spectrum → Submodule C (C ⊗[ℚ] U) := fun i => HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace TA (χ i)
  have hS : DirectSum.IsInternal S :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hinternal.submodule_iSupIndep hinternal.submodule_iSup_eq_top
  let Q : Spectrum → Module.End C (C ⊗[ℚ] U) := HeckeCycles.HeckeCharacters.CM.Projectors.projector S hS
  let q : Spectrum → C ⊗[ℚ] (U →ₗ[ℚ] U) :=
    fun i => (ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv C U U).symm (Q i)
  obtain ⟨K, hKnumber, hKgalois, hEK, hlift⟩ := HeckeCycles.Coefficients.CM.finite_galois_field_for_tensors E C q
  let : NumberField K := hKnumber
  choose p hp using hlift
  let P : Spectrum → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) :=
    fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i)
  have hext : ∀ i, P i = HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector C U TA χ hS i := by
    intro i
    change ComplexMultiplication.HomBaseChange.CM.homBaseChange ℂ U U (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K (U →ₗ[ℚ] U) (p i)) =
      HeckeCycles.ScalarConjugate.CM.Extension.extendEnd C U (Q i)
    rw [hp i]
    exact (HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_eq_complexHom C U (Q i)).symm
  have hsum : ∀ x, ∑ i, P i x = x := by
    intro x
    simp_rw [hext]
    exact HeckeCycles.ScalarConjugate.CM.Extension.sum_extendedProjector C U TA χ hS x
  have hid : ∀ i, (P i).comp (P i) = P i := by
    intro i
    have ha : Q i * Q i = Q i := HeckeCycles.HeckeCharacters.CM.Projectors.projector_idempotent S hS i
    have he := congrArg (HeckeCycles.ScalarConjugate.CM.Extension.extendEnd C U) ha
    rw [map_mul] at he
    simpa only [hext, HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector, Q, S, Module.End.mul_eq_comp] using he
  have hh : ∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H := by
    intro i
    rw [hext]
    apply HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector_hodge C U TA χ hS hTA Subtype.val_injective H
    intro j
    rw [HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_rational]
    exact (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H H (T j)).mpr (hHodge j)
  have hr : ∀ i, LinearMap.range (P i) =
      HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ) (fun j => (χ i j : ℂ)) := by
    intro i
    rw [hext, HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector_range C U TA χ hS hTA Subtype.val_injective i]
    congr 1
    funext j
    exact HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_rational C U (T j)
  have hconj : ∀ i (σ : Gal(K/ℚ)),
      let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ (p i))
      ∃ τ : Gal(HeckeCycles.Coefficients.CM.algebraicField/ℚ),
        (∀ a : K, (τ (IntermediateField.inclusion (HeckeCycles.ScalarConjugate.CM.GaloisLift.le_algebraicField K) a) : ℂ) =
          (σ a : ℂ)) ∧ Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
        LinearMap.range Pσ = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ)
          (fun j => (τ (χ i j) : ℂ)) := by
    intro i σ
    obtain ⟨τ, hτ⟩ := HeckeCycles.ScalarConjugate.CM.GaloisLift.exists_algebraic_lift K σ
    have heq : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ (p i)) =
        ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients C U U
          (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ C (U →ₗ[ℚ] U) τ (q i)) :=
      congrArg (ComplexMultiplication.HomBaseChange.CM.homBaseChange ℂ U U)
        (HeckeCycles.ScalarConjugate.CM.GaloisLift.conjugate_inclusions_eq K (p i) (q i) (hp i) σ τ hτ)
    dsimp only
    refine ⟨τ, hτ, ?_, ?_⟩
    · rw [heq]
      exact HeckeCycles.ScalarConjugate.CM.SpectralConjugation.conjugated_spectral_projector_hodge C U T hcomm χ Subtype.val_injective
        hS H hHodge τ i
    · rw [heq]
      exact
        HeckeCycles.ScalarConjugate.CM.SpectralConjugation.conjugated_spectral_projector_range C U T hcomm χ Subtype.val_injective hS τ i
  have hPc : ∀ i j, Commute (P i) ((T j).baseChange ℂ) := by
    intro i j
    have h := HeckeCycles.ScalarConjugate.CM.Extension.extendedProjector_commutes C U TA χ hS hTA i j
    rw [← hext i, HeckeCycles.ScalarConjugate.CM.Extension.extendEnd_rational] at h
    exact h
  let Active := {i : Spectrum // ∃ φ, P i (theta φ) ≠ 0}
  let e := Fintype.equivFin Active
  refine ⟨K, hKnumber, hKgalois, hEK, HeckeCycles.ScalarConjugate.CM.GaloisLift.le_algebraicField K, Fintype.card Active,
    (fun i => p (e.symm i).val), (fun i => χ (e.symm i).val),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hid (e.symm i).val
  · intro i
    exact HeckeCycles.Coefficients.CM.extended_range_eq_conjugateSpace K (p (e.symm i).val)
  · intro i
    exact hh (e.symm i).val
  · intro i j
    exact hPc (e.symm i).val j
  · intro i
    exact (e.symm i).property
  · intro φ
    calc
      _ = ∑ i : Active, P i.val (theta φ) :=
        Equiv.sum_comp e.symm (fun i : Active => P i.val (theta φ))
      _ = theta φ := HeckeCycles.Projectors.CM.sum_active_operators P hsum theta φ
  · intro i
    exact hr (e.symm i).val
  · intro i σ
    exact hconj (e.symm i).val σ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingProjectors.Spectral
