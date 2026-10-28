import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Field Oscillator -/

namespace OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction

noncomputable section

section

/-! Transport of the independently defined oscillator and bare metaplectic groups. -/

open _root_.Matrix

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
  [SecondCountableTopology k] [SecondCountableTopology l]

def fieldOscillatorTransport (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) : FunctionsMetaplectic.Construction.Oscillator k n ψ →* FunctionsMetaplectic.Construction.Oscillator l n (FieldFourier.Construction.fieldCharacter e ψ) where
  toFun a := by
    let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
    refine ⟨(FieldFourier.Construction.fieldSymplecticMap e n a.val.1, C.symm.trans (a.val.2.trans C)), ?_, ?_⟩
    · intro f
      have h := FieldCoordinates.Construction.testSpaceTransport_energy_congr (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
        (a.val.2 (C.symm f)) (C.symm f) (a.property.1 (C.symm f))
      change FunctionsMetaplectic.Construction.l2Energy l n (C (a.val.2 (C.symm f))) = FunctionsMetaplectic.Construction.l2Energy l n f
      exact h.trans (congrArg (FunctionsMetaplectic.Construction.l2Energy l n) (C.apply_symm_apply f))
    · intro v f h
      have hv : (fun i => e (e.symm (v i))) = v := by ext i; exact e.apply_symm_apply _
      obtain ⟨f, rfl⟩ := C.surjective f
      obtain ⟨h, rfl⟩ := C.surjective h
      change FunctionsMetaplectic.Construction.heisenbergGraph (FieldFourier.Construction.fieldCharacter e ψ) v (C f) (C h) ↔
        FunctionsMetaplectic.Construction.heisenbergGraph (FieldFourier.Construction.fieldCharacter e ψ) (FunctionsMetaplectic.Construction.symplecticAction (FieldFourier.Construction.fieldSymplecticMap e n a.val.1) v)
          (C (a.val.2 (C.symm (C f)))) (C (a.val.2 (C.symm (C h))))
      rw [C.symm_apply_apply, C.symm_apply_apply, ← hv, FieldFourier.Construction.fieldSymplecticMap_action,
        ← FieldFourier.Construction.fieldHeisenbergGraph e he he', ← FieldFourier.Construction.fieldHeisenbergGraph e he he']
      exact a.property.2 (fun i => e.symm (v i)) f h
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact (FieldFourier.Construction.fieldSymplecticMap e n).map_one
    · let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
      apply LinearEquiv.ext
      intro f
      change C (C.symm f) = f
      exact C.apply_symm_apply f
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact (FieldFourier.Construction.fieldSymplecticMap e n).map_mul a.val.1 b.val.1
    · let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
      apply LinearEquiv.ext
      intro f
      change C (a.val.2 (b.val.2 (C.symm f))) =
        C (a.val.2 (C.symm (C (b.val.2 (C.symm f)))))
      rw [C.symm_apply_apply]

theorem fieldOscillatorTransport_apply (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (fieldOscillatorTransport e he he' n ψ a).val.2
      (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f) =
        FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) (a.val.2 f) := by
  let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
  change C (a.val.2 (C.symm (C f))) = C (a.val.2 f)
  rw [C.symm_apply_apply]

theorem fieldOscillatorTransport_projection (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Oscillator k n ψ) :
    OscillatorProjection.Construction.oscillatorProjection l n (FieldFourier.Construction.fieldCharacter e ψ) (fieldOscillatorTransport e he he' n ψ a) =
      FieldFourier.Construction.fieldSymplecticMap e n (OscillatorProjection.Construction.oscillatorProjection k n ψ a) := rfl

theorem fieldOscillatorTransport_minus (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) :
    fieldOscillatorTransport e he he' n ψ (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) =
      FunctionsMetaplectic.Construction.oscillatorMinus l n (FieldFourier.Construction.fieldCharacter e ψ) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (FieldFourier.Construction.fieldSymplecticMap e n).map_one
  · let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
    apply LinearEquiv.ext
    intro f
    change C (-(C.symm f)) = -f
    rw [map_neg, C.apply_symm_apply]

theorem fieldOscillatorTransport_bare (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) :
    fieldOscillatorTransport e he he' n ψ a.val ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup l n (FieldFourier.Construction.fieldCharacter e ψ) := by
  let F := fieldOscillatorTransport e he he' n ψ
  have hle : FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ ≤ (FunctionsMetaplectic.Construction.metaplecticSubgroup l n (FieldFourier.Construction.fieldCharacter e ψ)).comap F := by
    change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    change F x ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup l n (FieldFourier.Construction.fieldCharacter e ψ)
    rcases hx with hx | hx
    · obtain ⟨a, b, rfl⟩ := mem_commutatorSet_iff.mp hx
      rw [map_commutatorElement]
      exact Subgroup.subset_closure (Or.inl (commutator_mem_commutatorSet _ _))
    · obtain rfl := Set.mem_singleton_iff.mp hx
      rw [fieldOscillatorTransport_minus]
      exact Subgroup.subset_closure (Or.inr rfl)
  exact hle a.property

def fieldMetaplecticTransport (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) : FunctionsMetaplectic.Construction.Metaplectic l n (FieldFourier.Construction.fieldCharacter e ψ) :=
  ⟨fieldOscillatorTransport e he he' n ψ a.val, fieldOscillatorTransport_bare e he he' n ψ a⟩

theorem fieldMetaplecticTransport_scalar_pullback
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (z : ℂ)
    (h : ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat l n, (fieldMetaplecticTransport e he he' n ψ a).val.val.2 f = z • f)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : a.val.val.2 f = z • f := by
  let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
  have hh := h (C f)
  change C (a.val.val.2 (C.symm (C f))) = z • C f at hh
  rw [C.symm_apply_apply] at hh
  apply C.injective
  rw [map_smul]
  exact hh

end

/-! Pullback of actual bare metaplectic elements along a topological field isomorphism. -/

def metaplecticCharacterCongr
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) : FunctionsMetaplectic.Construction.Metaplectic k n ψ ≃* FunctionsMetaplectic.Construction.Metaplectic k n η := by
  subst η
  exact MulEquiv.refl _

theorem metaplecticCharacterCongr_projection
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) :
    FunctionsMetaplectic.Construction.metaplecticProjection k n η (metaplecticCharacterCongr h a) = FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a := by
  subst η
  rfl

theorem metaplecticCharacterCongr_operator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) :
    (metaplecticCharacterCongr h a).val.val.2 = a.val.val.2 := by
  subst η
  rfl

theorem fieldCharacter_symm {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (ψ : AddChar k ℂ) : FieldFourier.Construction.fieldCharacter e.symm (FieldFourier.Construction.fieldCharacter e ψ) = ψ := by
  ext x
  change ψ (e.symm (e x)) = ψ x
  rw [e.symm_apply_apply]

theorem fieldSymplecticMap_symm {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (n : ℕ) (g : FunctionsMetaplectic.Construction.Symplectic k n) :
    FieldFourier.Construction.fieldSymplecticMap e.symm n (FieldFourier.Construction.fieldSymplecticMap e n g) = g := by
  apply Subtype.ext
  ext i j
  exact e.symm_apply_apply (g.val i j)

variable {k l : Type} [NormedField k] [NormedField l]
  [LocallyCompactSpace k] [LocallyCompactSpace l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
  [SecondCountableTopology k] [SecondCountableTopology l]

def fieldMetaplecticPullback (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic l n (FieldFourier.Construction.fieldCharacter e ψ)) : FunctionsMetaplectic.Construction.Metaplectic k n ψ :=
  metaplecticCharacterCongr (fieldCharacter_symm e ψ)
    (fieldMetaplecticTransport e.symm he' he n (FieldFourier.Construction.fieldCharacter e ψ) a)

theorem fieldMetaplecticPullback_projection
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic l n (FieldFourier.Construction.fieldCharacter e ψ)) :
    FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (fieldMetaplecticPullback e he he' n ψ a) =
      FieldFourier.Construction.fieldSymplecticMap e.symm n (FunctionsMetaplectic.Construction.metaplecticProjection l n (FieldFourier.Construction.fieldCharacter e ψ) a) := by
  rw [fieldMetaplecticPullback, metaplecticCharacterCongr_projection]
  rfl

theorem fieldMetaplecticPullback_operator
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic l n (FieldFourier.Construction.fieldCharacter e ψ))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (fieldMetaplecticPullback e he he' n ψ a).val.val.2 f =
      (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)).symm
        (a.val.val.2 (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f)) := by
  rw [fieldMetaplecticPullback, metaplecticCharacterCongr_operator]
  rfl

theorem fieldMetaplecticPullback_apply
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ) (a : FunctionsMetaplectic.Construction.Metaplectic l n (FieldFourier.Construction.fieldCharacter e ψ))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (FunctionsMetaplectic.Construction.weilRepresentation k n ψ (fieldMetaplecticPullback e he he' n ψ a) f).val x =
      (FunctionsMetaplectic.Construction.weilRepresentation l n (FieldFourier.Construction.fieldCharacter e ψ) a
        (FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n) f)).val (fun i => e (x i)) := by
  change ((fieldMetaplecticPullback e he he' n ψ a).val.val.2 f).val x = _
  rw [fieldMetaplecticPullback_operator]
  rfl

theorem field_metaplecticProjection_surjective
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm)
    (n : ℕ) (ψ : AddChar k ℂ)
    (hs : Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection l n (FieldFourier.Construction.fieldCharacter e ψ))) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) := by
  intro g
  obtain ⟨a, ha⟩ := hs (FieldFourier.Construction.fieldSymplecticMap e n g)
  refine ⟨fieldMetaplecticPullback e he he' n ψ a, ?_⟩
  rw [fieldMetaplecticPullback_projection, ha, fieldSymplecticMap_symm]

end

end OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction
