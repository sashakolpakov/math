import OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport

/-! # Archimedean Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanFourier.Construction

noncomputable section

/-! The unitary Fourier generator transported through a real field isomorphism. -/

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [CharZero F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F)
variable (e : ℝ ≃+* F) (he : Continuous e) (hei : Continuous e.symm)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1)

omit [MeasurableSpace F] [BorelSpace F] in
theorem realFieldTestEquiv_heisenberg (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    FieldCoordinates.Construction.crossFieldTestEquiv (FieldCoordinates.Construction.coordinateFieldEquiv (Fin d) e he hei)
      (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
    HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete
      (ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom) (hc.comp he) (fun t => hu (e t))
      ((FieldCoordinates.Construction.coordinateFieldEquiv (Fin d ⊕ Fin d) e he hei).symm v)
      (FieldCoordinates.Construction.crossFieldTestEquiv (FieldCoordinates.Construction.coordinateFieldEquiv (Fin d) e he hei) f) := by
  apply Subtype.ext
  exact FieldCoordinates.Construction.heisenberg_field_coordinates e he hei ψ v f.val

include hF e he hei in
theorem exists_archimedean_unitary_fourier (hn : ∃ t, ψ t ≠ 1) :
    ∃ U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) ∧
      (∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
        HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (FourierCovariance.Construction.fourierPhaseRotation v) (U f)) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let χ := ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  have hχn : ∃ t, χ t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e.symm t, ?_⟩
    change ψ (e (e.symm t)) ≠ 1
    rwa [e.apply_symm_apply]
  obtain ⟨UR, henergy, hcov⟩ := RealFourierUnitary.Construction.exists_real_unitary_fourier χ (hc.comp he)
    (fun t => hu (e t)) hχn (d := d)
  let a := FieldCoordinates.Construction.coordinateFieldEquiv (Fin d) e he hei
  let C := FieldCoordinates.Construction.crossFieldTestEquiv a
  let U := (C.trans UR).trans C.symm
  have hcancel (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : C (U f) = UR (C f) := C.apply_symm_apply _
  have hC (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      C (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
        HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete χ (hc.comp he) (fun t => hu (e t))
          ((FieldCoordinates.Construction.coordinateFieldEquiv (Fin d ⊕ Fin d) e he hei).symm v) (C f) :=
    realFieldTestEquiv_heisenberg hF e he hei ψ hc hu v f
  refine ⟨U, FieldCoordinates.Construction.crossFieldTestEquiv_transport_unitary a UR henergy, ?_⟩
  intro v f
  apply C.injective
  rw [hcancel, hC, hcov, hC, hcancel]
  congr 2
  funext i
  cases i with
  | inl j => rfl
  | inr j => exact (map_neg e.symm (v (Sum.inl j))).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanFourier.Construction
