import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.MinkowskiSelfAdjointRealization
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Bracket Operator Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketOperatorEquiv.Construction

noncomputable section

/-! Matrix and operator realizations of the actual Minkowski bracket group. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

theorem matrixFrameAction_continuousEndMatrixUnitsEquiv
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (x : L) :
    LatticeFrameAction.Construction.matrixFrameAction b (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b g) x = g.val x := by
  change (LatticeFrameAction.Construction.matrixFrameAction b (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b g)).toLinearMap x = _
  rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
  change Matrix.toLin b b (LinearMap.toMatrix b b g.val.toLinearMap) x = _
  rw [Matrix.toLin_toMatrix]
  rfl

local instance lieMixedSpan_normed_uniform_for_operator_equiv
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_operator_equiv
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

variable {k : Type} [Field k] [NumberField k] {n m : ℕ}
  (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
  (b : Module.Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G))

theorem continuousEndMatrixUnitsEquiv_mem_lieBracket_iff
    (g : (MixedLattice.Construction.lieMixedSpan G →L[ℝ] MixedLattice.Construction.lieMixedSpan G)ˣ) :
    ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b g ∈ BracketStabilizer.Construction.lieBracketMatrixGroup G hG b ↔
      g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) := by
  rw [BracketStabilizer.Construction.lieBracketMatrixGroup, Integral.TensorStabilizer.Construction.mem_multilinearOperationStabilizer_iff]
  constructor
  · intro h x y
    have he := h ![x, y]
    simpa only [matrixFrameAction_continuousEndMatrixUnitsEquiv] using! he
  · intro h v
    simp only [matrixFrameAction_continuousEndMatrixUnitsEquiv]
    exact h (v 0) (v 1)

def lieBracketOperatorHom : BracketStabilizer.Construction.lieBracketMatrixGroup G hG b →*
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) where
  toFun g := ⟨(ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm g.val, by
    apply (continuousEndMatrixUnitsEquiv_mem_lieBracket_iff G hG b _).mp
    simpa only [ContinuousMulEquiv.apply_symm_apply] using g.property⟩
  map_one' := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm.map_one
  map_mul' g h := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm.map_mul g.val h.val

def lieBracketOperatorBackHom : UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) →*
    BracketStabilizer.Construction.lieBracketMatrixGroup G hG b where
  toFun g := ⟨ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b g.val,
    (continuousEndMatrixUnitsEquiv_mem_lieBracket_iff G hG b g.val).mpr g.property⟩
  map_one' := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).map_one
  map_mul' g h := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).map_mul g.val h.val

def lieBracketOperatorEquiv : BracketStabilizer.Construction.lieBracketMatrixGroup G hG b ≃ₜ*
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) where
  toFun := lieBracketOperatorHom G hG b
  invFun := lieBracketOperatorBackHom G hG b
  left_inv g := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).apply_symm_apply g.val
  right_inv g := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm_apply_apply g.val
  map_mul' := (lieBracketOperatorHom G hG b).map_mul
  continuous_toFun := ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).continuous.comp continuous_subtype_val).subtype_mk _

theorem lieBracketOperatorEquiv_apply (g : BracketStabilizer.Construction.lieBracketMatrixGroup G hG b) (x : MixedLattice.Construction.lieMixedSpan G) :
    (lieBracketOperatorEquiv G hG b g).val.val x = LatticeFrameAction.Construction.matrixFrameAction b g.val x := by
  have he := matrixFrameAction_continuousEndMatrixUnitsEquiv b
    ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm g.val) x
  rw [ContinuousMulEquiv.apply_symm_apply] at he
  exact he.symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketOperatorEquiv.Construction
