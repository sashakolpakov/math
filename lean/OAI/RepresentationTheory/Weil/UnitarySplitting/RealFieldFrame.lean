import OAI.RepresentationTheory.Weil.UnitarySplitting.CircleFieldTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.Characters

/-! # Real Field Frame -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealFieldFrame.Construction

noncomputable section

/-! The trace tensor frame and prescribed characters in real scalar coordinates. -/

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [Algebra ℝ F] [Algebra ℝ E] [IsScalarTower ℝ F E]

theorem realField_algebraMap_comp (e : ℝ ≃ₐ[ℝ] F) :
    (algebraMap F E).comp e.toRingEquiv.toRingHom = algebraMap ℝ E := by
  ext t
  change algebraMap F E (e t) = algebraMap ℝ E t
  rw [show e t = algebraMap ℝ F t from e.commutes t, IsScalarTower.algebraMap_apply ℝ F E]

def realFieldCoordinateLinearEquiv (e : ℝ ≃ₐ[ℝ] F) (I : Type) :
    (I → F) ≃ₗ[ℝ] (I → ℝ) := LinearEquiv.piCongrRight (fun _ : I => e.symm.toLinearEquiv)

def realFieldSymplecticFrame (e : ℝ ≃ₐ[ℝ] F) {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) : Oscillator.Construction.SymplecticFrame (σ.restrictScalars ℝ) H K where
  coordinates := (c.coordinates.restrictScalars ℝ).trans
    (realFieldCoordinateLinearEquiv e (Fin (m * n) ⊕ Fin (m * n)))
  preserves := by
    intro x y
    have ht := Algebra.trace_eq_of_ringEquiv e.toRingEquiv (realField_algebraMap_comp (E := E) e)
      (DualPair.Construction.sesquilinear σ (H.kronecker K) x y)
    change e (Algebra.trace ℝ E (DualPair.Construction.sesquilinear (σ.restrictScalars ℝ) (H.kronecker K) x y)) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ (H.kronecker K) x y) at ht
    apply e.injective
    change e (∑ i, (e.symm (c.coordinates x (Sum.inr i)) * e.symm (c.coordinates y (Sum.inl i)) -
      e.symm (c.coordinates x (Sum.inl i)) * e.symm (c.coordinates y (Sum.inr i)))) =
        e (Algebra.trace ℝ E (DualPair.Construction.sesquilinear (σ.restrictScalars ℝ) (H.kronecker K) x y) / 2)
    simp only [map_sum, map_sub, map_mul, map_div₀, map_ofNat, e.apply_symm_apply]
    rw [ht]
    exact c.preserves x y

theorem realFieldSymplecticFrame_coordinates (e : ℝ ≃ₐ[ℝ] F)
    (he : Continuous e) (hei : Continuous e.symm) {m n : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (v : (Fin m × Fin n) → E) :
    (realFieldSymplecticFrame e σ H K c).coordinates v =
      (FieldCoordinates.Construction.coordinateFieldEquiv (Fin (m * n) ⊕ Fin (m * n)) e.toRingEquiv he hei).symm (c.coordinates v) := rfl

def realFieldUnitHom (e : ℝ ≃ₐ[ℝ] F) (he : Continuous e) : ℝˣ →ₜ* Fˣ :=
  ⟨Units.map e.toMonoidHom, Units.continuous_map he⟩

def realFieldSplittingCharacters (e : ℝ ≃ₐ[ℝ] F) (he : Continuous e) {m n : ℕ}
    (characters : Characters.Construction.SplittingCharacters F E m n) : Characters.Construction.SplittingCharacters ℝ E m n where
  quadratic := characters.quadratic.comp (realFieldUnitHom e he)
  quadratic_kernel := by
    intro a
    have hn (b : Eˣ) := Algebra.norm_eq_of_ringEquiv e.toRingEquiv
      (realField_algebraMap_comp (E := E) e) (b : E)
    change characters.quadratic (Units.map e.toMonoidHom a) = 1 ↔ _
    rw [characters.quadratic_kernel]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, e.injective ?_⟩
      exact (hn b).trans hb
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      change Algebra.norm F (b : E) = e (a : ℝ)
      rw [← hn b, hb]
      rfl
  hermitian := characters.hermitian
  skewHermitian := characters.skewHermitian
  hermitian_restriction := by
    intro a
    have hh := characters.hermitian_restriction (Units.map e.toMonoidHom a)
    change characters.hermitian (Units.map (algebraMap ℝ E).toMonoidHom a) =
      characters.quadratic (Units.map e.toMonoidHom a) ^ m
    convert hh using 2
    apply Units.ext
    exact congrArg (fun f : ℝ →+* E => f (a : ℝ)) (realField_algebraMap_comp (E := E) e).symm
  skewHermitian_restriction := by
    intro a
    have hh := characters.skewHermitian_restriction (Units.map e.toMonoidHom a)
    change characters.skewHermitian (Units.map (algebraMap ℝ E).toMonoidHom a) =
      characters.quadratic (Units.map e.toMonoidHom a) ^ n
    convert hh using 2
    apply Units.ext
    exact congrArg (fun f : ℝ →+* E => f (a : ℝ)) (realField_algebraMap_comp (E := E) e).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealFieldFrame.Construction
