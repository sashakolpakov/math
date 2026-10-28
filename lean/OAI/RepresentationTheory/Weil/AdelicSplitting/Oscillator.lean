import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Oscillator -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction

noncomputable section

/-! Local circle-scalar oscillator groups and their actual scalar operators.
The underlying group is LocalWeil's independently constructed Heisenberg
intertwiner group, rather than an arbitrary central extension. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ψ : AddChar k ℂ)

abbrev LocalCover := Local.FunctionsMetaplectic.Construction.Oscillator k n ψ

def localProjection : LocalCover k n ψ →* Local.FunctionsMetaplectic.Construction.Symplectic k n :=
  (MonoidHom.fst _ _).comp (Local.FunctionsMetaplectic.Construction.oscillatorSubgroup k n ψ).subtype

def localOperator : LocalCover k n ψ →* (Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :=
  (MonoidHom.snd _ _).comp (Local.FunctionsMetaplectic.Construction.oscillatorSubgroup k n ψ).subtype

def scalarLinear (z : Circle) : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  LinearEquiv.smulOfUnit (Circle.toUnits z)

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
@[simp] theorem scalarLinear_apply (z : Circle) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    scalarLinear k n z f = (z : ℂ) • f := rfl

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
theorem heisenberg_smul (z : ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (z • f) = z • Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f := by
  funext x
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction, mul_left_comm]

def scalarElement (z : Circle) : LocalCover k n ψ := by
  refine ⟨(1, scalarLinear k n z), ?_⟩
  constructor
  · intro f
    unfold Local.FunctionsMetaplectic.Construction.l2Energy
    congr 1
    funext x
    change ‖(z : ℂ) * f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
    rw [norm_mul, Circle.norm_coe, one_mul]
  · intro v f h
    change h.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val ↔
      (scalarLinear k n z h).val =
        Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction 1 v) (scalarLinear k n z f).val
    rw [Local.FunctionsMetaplectic.Construction.symplecticAction_one]
    change h.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val ↔
      (z : ℂ) • h.val = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v ((z : ℂ) • f.val)
    rw [heisenberg_smul]
    constructor
    · intro hh; rw [hh]
    · intro hh
      have hh' := congrArg (fun f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ => (z : ℂ)⁻¹ • f) hh
      simpa only [smul_smul, inv_mul_cancel₀ z.coe_ne_zero, one_smul] using hh'

def localScalar : Circle →* LocalCover k n ψ where
  toFun := scalarElement k n ψ
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
    · change (1 : Local.FunctionsMetaplectic.Construction.Symplectic k n) = 1 * 1
      simp
    · apply LinearEquiv.ext
      intro f
      change ((z * w : Circle) : ℂ) • f = (z : ℂ) • ((w : ℂ) • f)
      rw [Circle.coe_mul, mul_smul]

@[simp] theorem localProjection_scalar (z : Circle) :
    localProjection k n ψ (localScalar k n ψ z) = 1 := rfl

@[simp] theorem localOperator_scalar (z : Circle) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    localOperator k n ψ (localScalar k n ψ z) f = (z : ℂ) • f := rfl

theorem localScalar_central (z : Circle) (g : LocalCover k n ψ) :
    Commute (localScalar k n ψ z) g := by
  change localScalar k n ψ z * g = g * localScalar k n ψ z
  apply Subtype.ext
  apply Prod.ext
  · simp [localScalar, scalarElement]
  · apply LinearEquiv.ext
    intro f
    change (z : ℂ) • g.val.2 f = g.val.2 ((z : ℂ) • f)
    exact (g.val.2.map_smul (z : ℂ) f).symm

/-- The stabilizer of a specified actual test function is a subgroup. -/
def vacuumStabilizer (φ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Subgroup (LocalCover k n ψ) where
  carrier := {g | localOperator k n ψ g φ = φ}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.val.2 (h.val.2 φ) = φ
    rw [show h.val.2 φ = φ from hh, show g.val.2 φ = φ from hg]
  inv_mem' := by
    intro g hg
    change g.val.2.symm φ = φ
    have h := congrArg g.val.2.symm (show g.val.2 φ = φ from hg)
    simpa using h.symm

/-- Strong L² observations of both operator directions, following the
checked UnitarySplitting construction. -/
def localObservations (g : LocalCover k n ψ) :
    Local.FunctionsMetaplectic.Construction.Symplectic k n ×
      ((Local.FunctionsMetaplectic.Construction.schwartzBruhat k n × Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) → ℝ) ×
      ((Local.FunctionsMetaplectic.Construction.schwartzBruhat k n × Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) → ℝ) :=
  (g.val.1,
    fun p => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k n (g.val.2 p.1 - p.2)),
    fun p => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k n (g.val.2.symm p.1 - p.2)))

instance localCoverTopology : TopologicalSpace (LocalCover k n ψ) :=
  TopologicalSpace.induced (localObservations k n ψ) inferInstance

theorem localProjection_continuous : Continuous (localProjection k n ψ) := by
  have h : Continuous (localObservations k n ψ) :=
    continuous_induced_dom
  change Continuous (fun g => (localObservations k n ψ g).1)
  exact continuous_fst.comp h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction
