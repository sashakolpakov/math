import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.AdjointOperator
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.CharacteristicInvariant
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap

/-! # Lie Bracket Uniform Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracketUniformGap.Construction

noncomputable section

section

/-! Integral matrix coordinates and conjugation covariance of the
intrinsic adjoint operators on the Minkowski Lie space. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

def lieMixedAdjointMatrix
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    Lie.MixedLattice.Construction.lieMixedSpan G →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
  (LinearMap.toMatrix b b).toLinearMap.comp (AdjointOperator.Construction.lieMixedAdjointLinear G hG)

theorem lieMixedAdjointMatrix_integral
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))
    (hb : Submodule.span ℤ (Set.range b) = Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) (hA : A ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) :
    ∃ M : Matrix (Fin m) (Fin m) ℤ, M.map (Int.castRingHom ℝ) = lieMixedAdjointMatrix G hG b A := by
  have hc (i j : Fin m) : ∃ z : ℤ, algebraMap ℤ ℝ z = b.repr (AdjointOperator.Construction.lieMixedAdjoint G hG A (b j)) i := by
    apply (b.mem_span_iff_repr_mem ℤ _).mp
    rw [hb]
    apply LieBracket.Construction.lieMixedBracket_integral G hG A (b j) hA
    rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self j)
  choose M hM using hc
  refine ⟨Matrix.of M, ?_⟩
  ext i j : 1
  change (M i j : ℝ) = LinearMap.toMatrix b b (AdjointOperator.Construction.lieMixedAdjoint G hG A) i j
  rw [LinearMap.toMatrix_apply']
  exact hM i j

theorem nilpotent_of_lieMixedAdjointMatrix_nilpotent
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) (A : Lie.MixedLattice.Construction.lieMixedSpan G)
    (hA : IsNilpotent (lieMixedAdjointMatrix G hG b A)) : IsNilpotent (AdjointOperator.Construction.lieMixedAdjoint G hG A) := by
  have h := hA.map (Matrix.toLinAlgEquiv b)
  change IsNilpotent (Matrix.toLin b b (LinearMap.toMatrix b b (AdjointOperator.Construction.lieMixedAdjoint G hG A))) at h
  rwa [Matrix.toLin_toMatrix] at h

theorem matrixFrameAction_toMatrix
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (g : Matrix.GeneralLinearGroup ι ℝ) :
    LinearMap.toMatrix b b (LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap = g.val := by
  rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap, LinearMap.toMatrix_toLin]

theorem lieMixedAdjointMatrix_conjugate
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) (hg : g ∈ Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) :
    lieMixedAdjointMatrix G hG b (LatticeFrameAction.Construction.matrixFrameAction b g A) =
      g.val * lieMixedAdjointMatrix G hG b A * (g⁻¹).val := by
  have hpres := (Integral.TensorStabilizer.Construction.mem_multilinearOperationStabilizer_iff b 2 (LieBracket.Construction.lieMixedBracketForm G hG) g).mp hg
  have he : (LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap * AdjointOperator.Construction.lieMixedAdjoint G hG A =
      AdjointOperator.Construction.lieMixedAdjoint G hG (LatticeFrameAction.Construction.matrixFrameAction b g A) * (LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap := by
    apply LinearMap.ext
    intro B
    exact hpres ![A, B]
  have hm := congrArg (LinearMap.toMatrix b b) he
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, matrixFrameAction_toMatrix] at hm
  have hmi := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M * (g⁻¹).val) hm
  have hi : g.val * (g⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel g)
  rw [Matrix.mul_assoc _ g.val, hi, Matrix.mul_one] at hmi
  exact hmi.symm

end

/-! Intrinsic adjoint characteristic coefficients give a uniform
vector gap for all automorphisms of the anisotropic Minkowski Lie bracket. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

theorem integer_vector_range_discrete (m : ℕ) :
    IsDiscrete (Set.range (fun z : Fin m → ℤ => fun i => (z i : ℝ))) := by
  have he : Topology.IsEmbedding (fun z : Fin m → ℤ => fun i => (z i : ℝ)) :=
    Topology.IsEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real.isEmbedding)
  exact he.isDiscrete_range

theorem anisotropic_bracket_group_uniform_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) {m : ℕ}
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup))
    (hb : Submodule.span ℤ (Set.range b) = Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G.matrixGroup G.connected b,
      ∀ x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b g.val x‖ := by
  let P : Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup → (Fin (m + 1) → ℝ) :=
    fun x => CharacteristicInvariant.Construction.characteristicInvariant (lieMixedAdjointMatrix G.matrixGroup G.connected b x)
  let D := Set.range (fun z : Fin (m + 1) → ℤ => fun i => (z i : ℝ))
  have hP : Continuous P := CharacteristicInvariant.Construction.continuous_characteristicInvariant.comp
    (lieMixedAdjointMatrix G.matrixGroup G.connected b).continuous_of_finiteDimensional
  have hP0 : P 0 = 0 := by
    change CharacteristicInvariant.Construction.characteristicInvariant (lieMixedAdjointMatrix G.matrixGroup G.connected b 0) = 0
    rw [map_zero, CharacteristicInvariant.Construction.characteristicInvariant_zero]
  have hD0 : (0 : Fin (m + 1) → ℝ) ∈ D := ⟨0, by ext; simp⟩
  have hvalues (x : Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup) (hx : x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)
      (hx0 : x ≠ 0) : P x ∈ D ∧ P x ≠ 0 := by
    obtain ⟨M, hM⟩ := lieMixedAdjointMatrix_integral G.matrixGroup G.connected b hb x hx
    refine ⟨?_, ?_⟩
    · change CharacteristicInvariant.Construction.characteristicInvariant (lieMixedAdjointMatrix G.matrixGroup G.connected b x) ∈ D
      rw [← hM, CharacteristicInvariant.Construction.characteristicInvariant_map]
      exact ⟨CharacteristicInvariant.Construction.characteristicInvariant M, rfl⟩
    · intro hz
      have hnil := CharacteristicInvariant.Construction.nilpotent_of_characteristicInvariant_eq_zero
        (lieMixedAdjointMatrix G.matrixGroup G.connected b x) hz
      exact hx0 (AdjointOperator.Construction.anisotropic_lieMixedAdjoint_nilpotent_lattice_eq_zero G haniso x hx
        (nilpotent_of_lieMixedAdjointMatrix_nilpotent G.matrixGroup G.connected b x hnil))
  apply InvariantGap.Construction.uniform_gap_of_discrete_invariant
    (fun g : Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G.matrixGroup G.connected b => LatticeFrameAction.Construction.matrixFrameAction b g.val)
    P hP hP0 D (integer_vector_range_discrete (m + 1)) hD0
    (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup) hvalues
  intro g x _
  change CharacteristicInvariant.Construction.characteristicInvariant (lieMixedAdjointMatrix G.matrixGroup G.connected b
      (LatticeFrameAction.Construction.matrixFrameAction b g.val x)) = _
  rw [lieMixedAdjointMatrix_conjugate G.matrixGroup G.connected b g.val g.property,
    CharacteristicInvariant.Construction.characteristicInvariant_conjugate]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracketUniformGap.Construction
