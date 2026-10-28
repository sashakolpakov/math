import OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair
import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Oscillator -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator.Construction

noncomputable section

/-!
The UnitarySplitting circle extension is the group of unitary Heisenberg intertwiners
on the actual Schwartz–Bruhat space, in symplectic coordinates. Coordinates
carry only a linear isometry condition, never a splitting. Existence of
coordinates, surjectivity, and the assertion that the kernel consists
exactly of circle scalars remain explicit conclusions of the target.
The topology records the symplectic component and strong L² convergence
of both operators and inverses; no discrete topology is substituted.
-/

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction _root_.MeasureTheory
open scoped BigOperators

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable {m n : ℕ}

/-- Weyl convention: [ (q,p), (q',p') ] = p·q' - q·p'. -/
def standardSymplecticPairing (d : ℕ) (x y : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : F :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))

/-- A polarization and symplectic coordinates for the trace tensor space.
This includes no operator, lift, or representation. -/
structure SymplecticFrame (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E) where
  coordinates : ((Fin m × Fin n) → E) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)
  preserves : ∀ x y,
    standardSymplecticPairing (m * n) (coordinates x) (coordinates y) =
      DualPair.Construction.traceTensorPairing σ H K x y

variable [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
variable (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)

abbrev TensorSymplectic := DualPair.Construction.pairingIsometries (DualPair.Construction.traceTensorPairing σ H K)
abbrev TestSpace := Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)

/-- Independently defined unitary Heisenberg intertwiners above the actual
symplectic group of the trace tensor pairing. -/
def circleExtensionSubgroup (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    Subgroup (TensorSymplectic σ H K ×
      (Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n))) where
  carrier := {a |
    (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (a.2 f) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f) ∧
    ∀ v f h, Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates v) f h ↔
      Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates (a.1.val v)) (a.2 f) (a.2 h)}
  one_mem' := by
    constructor
    · intro f; rfl
    · intro v f h; rfl
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro f
      change Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (a.2 (b.2 f)) = Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f
      rw [ha.1, hb.1]
    · intro v f h
      exact (hb.2 v f h).trans (ha.2 (b.1.val v) (b.2 f) (b.2 h))
  inv_mem' := by
    intro a ha
    constructor
    · intro f
      have h := ha.1 (a.2.symm f)
      simpa using h.symm
    · intro v f h
      have hh := ha.2 (a.1.val.symm v) (a.2.symm f) (a.2.symm h)
      simpa using hh.symm

abbrev CircleExtension (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :=
  circleExtensionSubgroup σ H K c ψ

/-- Strong L² observations of an operator and its inverse. -/
def oscillatorObservations (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ)
    (a : CircleExtension σ H K c ψ) :
    TensorSymplectic σ H K ×
      ((Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) × Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) → ℝ) ×
      ((Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) × Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) → ℝ) :=
  (a.val.1,
    (fun p => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (a.val.2 p.1 - p.2))),
    (fun p => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (a.val.2.symm p.1 - p.2))))

instance circleExtensionTopology (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    TopologicalSpace (CircleExtension σ H K c ψ) :=
  TopologicalSpace.induced (oscillatorObservations σ H K c ψ) inferInstance

def circleProjection (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    CircleExtension σ H K c ψ →ₜ* TensorSymplectic σ H K where
  toMonoidHom := (MonoidHom.fst _ _).comp (circleExtensionSubgroup σ H K c ψ).subtype
  continuous_toFun := by
    change Continuous (fun a : CircleExtension σ H K c ψ =>
      (oscillatorObservations σ H K c ψ a).1)
    exact continuous_fst.comp
      (continuous_induced_dom : Continuous (oscillatorObservations σ H K c ψ))

/-- The actual oscillator action is the operator component. -/
def oscillatorRepresentation (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    CircleExtension σ H K c ψ →*
      (Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :=
  (MonoidHom.snd _ _).comp (circleExtensionSubgroup σ H K c ψ).subtype

theorem oscillatorRepresentation_unitary (c : SymplecticFrame σ H K)
    (ψ : AddChar F ℂ) (a : CircleExtension σ H K c ψ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
    Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (oscillatorRepresentation σ H K c ψ a f) =
      Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) f := a.property.1 f

theorem oscillatorRepresentation_intertwines (c : SymplecticFrame σ H K)
    (ψ : AddChar F ℂ) (a : CircleExtension σ H K c ψ)
    (v : (Fin m × Fin n) → E) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
    Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates v) f h ↔
      Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (c.coordinates ((circleProjection σ H K c ψ a).val v))
        (oscillatorRepresentation σ H K c ψ a f)
        (oscillatorRepresentation σ H K c ψ a h) := a.property.2 v f h

omit σ H K in
def scalarOperator (d : ℕ) (z : Circle) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  LinearEquiv.smulOfUnit (Circle.toUnits z)

omit σ H K [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F] in
theorem scalarOperator_apply (d : ℕ) (z : Circle) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    scalarOperator (F := F) d z f = (z : ℂ) • f := rfl

omit σ H K [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F] in
theorem heisenbergFunction_smul (d : ℕ) (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (z : ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (z • f) = z • Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f := by
  funext x
  exact mul_left_comm _ _ _

omit σ H K in
theorem l2Energy_circle_smul (d : ℕ) (z : Circle) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d ((z : ℂ) • f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  unfold Local.FunctionsMetaplectic.Construction.l2Energy
  congr 1
  funext x
  change ‖(z : ℂ) * f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
  rw [norm_mul, Circle.norm_coe, one_mul]

/-- Circle scalars are actual scalar operators in the intertwiner group. -/
def circleScalar (c : SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    Circle →* CircleExtension σ H K c ψ where
  toFun z := ⟨(1, scalarOperator (m * n) z), by
    constructor
    · exact l2Energy_circle_smul (m * n) z
    · intro v f h
      change (h.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates v) f.val) ↔
        (z : ℂ) • h.val =
          Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates v) ((z : ℂ) • f.val)
      rw [heisenbergFunction_smul]
      constructor
      · intro hh; rw [hh]
      · intro hh
        have hh' := congrArg (fun f : Local.FunctionsMetaplectic.Construction.Position F (m * n) → ℂ => (z : ℂ)⁻¹ • f) hh
        simpa only [smul_smul, inv_mul_cancel₀ z.coe_ne_zero, one_smul] using hh'⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply LinearEquiv.ext
      intro f
      change (1 : ℂ) • f = f
      exact one_smul ℂ f
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · apply LinearEquiv.ext
      intro f
      change ((z * w : Circle) : ℂ) • f = (z : ℂ) • ((w : ℂ) • f)
      rw [Circle.coe_mul, mul_smul]

theorem circleScalar_projects_to_one (c : SymplecticFrame σ H K)
    (ψ : AddChar F ℂ) (z : Circle) :
    circleProjection σ H K c ψ (circleScalar σ H K c ψ z) = 1 := rfl

theorem circleScalar_central (c : SymplecticFrame σ H K)
    (ψ : AddChar F ℂ) (z : Circle) (a : CircleExtension σ H K c ψ) :
    circleScalar σ H K c ψ z * a = a * circleScalar σ H K c ψ z := by
  apply Subtype.ext
  apply Prod.ext
  · change 1 * a.val.1 = a.val.1 * 1
    simp
  · apply LinearEquiv.ext
    intro f
    change (z : ℂ) • a.val.2 f = a.val.2 ((z : ℂ) • f)
    exact (a.val.2.map_smul (z : ℂ) f).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator.Construction
