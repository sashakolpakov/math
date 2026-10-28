import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Transport Group Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.TransportGroupEquiv.Construction

noncomputable section

/-! Coordinate transport of the full topological bracket automorphism group. -/

variable {L V : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def continuousUnitTransport (e : L ≃L[ℝ] V) : (L →L[ℝ] L)ˣ ≃ₜ* (V →L[ℝ] V)ˣ :=
  Units.mapContinuousMulEquiv {
    toMulEquiv := e.conjContinuousAlgEquiv.toAlgEquiv.toMulEquiv
    continuous_toFun := e.conjContinuousAlgEquiv.continuous
    continuous_invFun := e.conjContinuousAlgEquiv.symm.continuous }

theorem continuousUnitTransport_apply (e : L ≃L[ℝ] V) (g : (L →L[ℝ] L)ˣ) (x : V) :
    (continuousUnitTransport e g).val x = e (g.val (e.symm x)) := rfl

theorem continuousUnitTransport_mem_bracket_iff (e : L ≃L[ℝ] V)
    (B : L →L[ℝ] L →L[ℝ] L) (g : (L →L[ℝ] L)ˣ) :
    continuousUnitTransport e g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport e B) ↔
      g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := by
  constructor
  · intro h x y
    have he := h (e x) (e y)
    simp only [continuousUnitTransport_apply, Positive.Killing.Construction.continuousBracketTransport_apply,
      ContinuousLinearEquiv.symm_apply_apply] at he
    exact e.injective he
  · intro h x y
    simp only [continuousUnitTransport_apply, Positive.Killing.Construction.continuousBracketTransport_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [h]

def bracketTransportGroupHom (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →* UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport e B) where
  toFun g := ⟨continuousUnitTransport e g.val, (continuousUnitTransport_mem_bracket_iff e B g.val).mpr g.property⟩
  map_one' := by apply Subtype.ext; exact (continuousUnitTransport e).map_one
  map_mul' g h := by apply Subtype.ext; exact (continuousUnitTransport e).map_mul g.val h.val

def bracketTransportGroupBackHom (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport e B) →* UnipotentBracketGroup.Construction.continuousBracketUnitGroup B where
  toFun g := ⟨(continuousUnitTransport e).symm g.val, by
    apply (continuousUnitTransport_mem_bracket_iff e B _).mp
    simpa only [ContinuousMulEquiv.apply_symm_apply] using g.property⟩
  map_one' := by apply Subtype.ext; exact (continuousUnitTransport e).symm.map_one
  map_mul' g h := by apply Subtype.ext; exact (continuousUnitTransport e).symm.map_mul g.val h.val

def bracketTransportGroupEquiv (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B ≃ₜ* UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Positive.Killing.Construction.continuousBracketTransport e B) where
  toFun := bracketTransportGroupHom e B
  invFun := bracketTransportGroupBackHom e B
  left_inv g := by apply Subtype.ext; exact (continuousUnitTransport e).symm_apply_apply g.val
  right_inv g := by apply Subtype.ext; exact (continuousUnitTransport e).apply_symm_apply g.val
  map_mul' g h := by apply Subtype.ext; exact (continuousUnitTransport e).map_mul g.val h.val
  continuous_toFun := ((continuousUnitTransport e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuousUnitTransport e).symm.continuous.comp continuous_subtype_val).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.TransportGroupEquiv.Construction
