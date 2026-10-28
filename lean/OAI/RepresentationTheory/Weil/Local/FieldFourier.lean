import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.OscillatorProjection

/-! # Field Fourier -/

namespace OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction

noncomputable section

section

/-! Field isomorphisms transport the concrete symplectic and Heisenberg actions. -/

open _root_.Matrix

def fieldCharacter {k l : Type} [Field k] [Field l] (e : k ≃+* l) (ψ : AddChar k ℂ) : AddChar l ℂ :=
  ψ.compAddMonoidHom e.symm.toAddMonoidHom

def fieldSymplecticMap {k l : Type} [Field k] [Field l] (e : k ≃+* l) (n : ℕ) :
    FunctionsMetaplectic.Construction.Symplectic k n →* FunctionsMetaplectic.Construction.Symplectic l n where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e.toRingHom⟩
  map_one' := by apply Subtype.ext; exact Matrix.map_one _ e.map_zero e.map_one
  map_mul' _ _ := by apply Subtype.ext; exact Matrix.map_mul

theorem fieldSymplecticMap_action {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    FunctionsMetaplectic.Construction.symplecticAction (fieldSymplecticMap e n g) (fun i => e (v i)) =
      fun i => e (FunctionsMetaplectic.Construction.symplecticAction g v i) := by
  ext i
  exact (RingHom.map_mulVec e.toRingHom g.val v i).symm

theorem fieldHeisenbergFunction {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergFunction (fieldCharacter e ψ) (fun i => e (v i))
      (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f).val =
      fun x => FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val (fun i => e.symm (x i)) := by
  funext x
  change ψ (e.symm (∑ i, e (v (Sum.inr i)) * (x i - e (v (Sum.inl i)) / 2))) *
    f.val (fun i => e.symm (x i - e (v (Sum.inl i)))) =
      ψ (∑ i, v (Sum.inr i) * (e.symm (x i) - v (Sum.inl i) / 2)) *
        f.val (fun i => e.symm (x i) - v (Sum.inl i))
  simp only [map_sum, map_mul, map_sub, map_div₀, map_ofNat, RingEquiv.symm_apply_apply]

theorem fieldHeisenbergGraph {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph (fieldCharacter e ψ) (fun i => e (v i))
        (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f)
        (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) h) := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [fieldHeisenbergFunction]
  constructor
  · intro hh
    ext x
    exact congrFun hh (fun i => e.symm (x i))
  · intro hh
    ext x
    have ht := congrFun hh (fun i => e (x i))
    change h.val (fun i => e.symm (e (x i))) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val (fun i => e.symm (e (x i))) at ht
    simpa only [RingEquiv.symm_apply_apply] using! ht

end

/-! Transport of the actual product measures and Fourier integrals between field presentations. -/

open _root_.MeasureTheory

variable {k l : Type} [NormedField k] [NormedField l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]

theorem field_productMeasure_map
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hmap : μ.map e = ν) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).map (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) =
      Measure.pi (fun _ : Fin n => ν) := by
  let : SigmaFinite (μ.map e) := hmap.symm ▸ inferInstance
  have hm := Measure.pi_map_pi (μ := fun _ : Fin n => μ) (f := fun _ => e)
    (fun _ => he.measurable.aemeasurable)
  simpa only [hmap] using! hm

theorem field_fourierIntegral
    [SecondCountableTopology k] [SecondCountableTopology l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hmap : μ.map e = ν) (n : ℕ) (ψ : AddChar k ℂ) (f : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (x : FunctionsMetaplectic.Construction.Position l n) :
    FunctionsMetaplectic.Construction.fourierIntegral (fieldCharacter e ψ) (Measure.pi (fun _ : Fin n => ν))
      (fun y => f (fun i => e.symm (y i))) x =
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (fun i => e.symm (x i)) := by
  let E := FieldCoordinates.Construction.fieldPositionEquiv e he he' n
  have hi := integral_map_equiv (μ := Measure.pi (fun _ : Fin n => μ))
    E.toHomeomorph.toMeasurableEquiv
      (fun y => f (E.symm y) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x y))
  have hm := field_productMeasure_map e he he' μ ν hmap n
  change (Measure.pi (fun _ : Fin n => μ)).map E.toHomeomorph.toMeasurableEquiv =
    Measure.pi (fun _ : Fin n => ν) at hm
  rw [hm] at hi
  change (∫ y, f (fun i => e.symm (y i)) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x y)
      ∂Measure.pi (fun _ : Fin n => ν)) =
    ∫ y, f (fun i => e.symm (e (y i))) * fieldCharacter e ψ (-FunctionsMetaplectic.Construction.dot x (fun i => e (y i)))
      ∂Measure.pi (fun _ : Fin n => μ) at hi
  rw [FunctionsMetaplectic.Construction.fourierIntegral, hi, FunctionsMetaplectic.Construction.fourierIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [RingEquiv.symm_apply_apply]
    congr 1
    change ψ (e.symm (-∑ i, x i * e (y i))) = ψ (-∑ i, e.symm (x i) * y i)
    rw [map_neg, map_sum]
    simp only [map_mul, RingEquiv.symm_apply_apply]

end

end OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction
