import OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction

/-! # Tensor Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.TensorStabilizer.Construction

noncomputable section

/-! An integral multilinear operation has a closed automorphism-group
image in the space of real lattices. -/

open scoped Classical
open _root_.Module MulAction

def multilinearOperationStabilizer
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (r : ℕ) (F : MultilinearMap ℝ (fun _ : Fin r => E) E) :
    Subgroup (Matrix.GeneralLinearGroup ι ℝ) :=
  (stabilizer (MultilinearMap ℝ (fun _ : Fin r => E) E ≃ₗ[ℝ]
    MultilinearMap ℝ (fun _ : Fin r => E) E) F).comap
      (MultilinearAction.Construction.multilinearCovariantRepresentation (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom r)

theorem mem_multilinearOperationStabilizer_iff
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (r : ℕ) (F : MultilinearMap ℝ (fun _ : Fin r => E) E)
    (g : Matrix.GeneralLinearGroup ι ℝ) :
    g ∈ multilinearOperationStabilizer b r F ↔
      ∀ v, LatticeFrameAction.Construction.matrixFrameAction b g (F v) = F (fun i => LatticeFrameAction.Construction.matrixFrameAction b g (v i)) := by
  change MultilinearAction.Construction.multilinearCovariantRepresentation (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom
    (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom r g F = F ↔ _
  constructor
  · intro h v
    have he := congrArg (fun f : MultilinearMap ℝ (fun _ : Fin r => E) E =>
      f (fun i => LatticeFrameAction.Construction.matrixFrameAction b g (v i))) h
    change LatticeFrameAction.Construction.matrixFrameAction b g (F (fun i => LatticeFrameAction.Construction.matrixFrameAction b g⁻¹ (LatticeFrameAction.Construction.matrixFrameAction b g (v i)))) = _ at he
    have hinv (x : E) : LatticeFrameAction.Construction.matrixFrameAction b g⁻¹ (LatticeFrameAction.Construction.matrixFrameAction b g x) = x := by
      rw [map_inv]
      exact (LatticeFrameAction.Construction.matrixFrameAction b g).symm_apply_apply x
    simpa only [hinv] using he
  · intro h
    apply MultilinearMap.ext
    intro v
    change LatticeFrameAction.Construction.matrixFrameAction b g (F (fun i => LatticeFrameAction.Construction.matrixFrameAction b g⁻¹ (v i))) = F v
    rw [h]
    congr 1
    funext i
    rw [map_inv]
    exact (LatticeFrameAction.Construction.matrixFrameAction b g).apply_symm_apply _

theorem continuous_matrixFrameAction_joint
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    Continuous (fun a : Matrix.GeneralLinearGroup ι ℝ × E => LatticeFrameAction.Construction.matrixFrameAction b a.1 a.2) := by
  have he (g : Matrix.GeneralLinearGroup ι ℝ) (x : E) :
      LatticeFrameAction.Construction.matrixFrameAction b g x = b.equivFun.symm (g.val.mulVec (b.equivFun x)) := by
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply]
    change (b.repr ((LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap x) : ι → ℝ) = _
    rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
    exact Matrix.repr_toLin b b g.val x
  simp_rw [he]
  exact b.equivFun.symm.continuous_of_finiteDimensional.comp
    ((Units.continuous_val.comp continuous_fst).matrix_mulVec
      (b.equivFun.continuous_of_finiteDimensional.comp continuous_snd))

theorem multilinearOperationStabilizer_quotient_image_closed
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (b : Basis ι ℝ E)
    (hb : Submodule.span ℤ (Set.range b) = Λ)
    (r : ℕ) (F : MultilinearMap ℝ (fun _ : Fin r => E) E)
    (hF : ∀ t : Fin r → ι, F (fun i => b (t i)) ∈ Λ) :
    let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ
    IsClosed ((QuotientGroup.mk : Matrix.GeneralLinearGroup ι ℝ → Matrix.GeneralLinearGroup ι ℝ ⧸ Γ) ''
      (multilinearOperationStabilizer b r F : Set (Matrix.GeneralLinearGroup ι ℝ))) := by
  let H := Matrix.GeneralLinearGroup ι ℝ
  let ρ := (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom
  let U := (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := E) b r).range
  let τ := MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ ρ b r
  let : MulAction H U := MulAction.compHom U τ
  have hρ : Continuous (fun a : H × E => ρ a.1 a.2) := continuous_matrixFrameAction_joint b
  let : ContinuousSMul H U := ⟨MultilinearAction.Construction.continuous_multilinearCovariantBasisRepresentation ρ ρ b r hρ hρ⟩
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ
  let x : U := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r F
  let L := MultilinearAction.Construction.integralMultilinearCoordinates b r Λ
  have hx : x ∈ L := (MultilinearAction.Construction.mem_integralMultilinearCoordinates b r Λ x).mpr hF
  have hΓ (g : H) (hg : g ∈ Γ) (v : E) (hv : v ∈ Λ) : ρ g v ∈ Λ :=
    ((StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ g).mp hg v).mpr hv
  have hΓb (g : H) (hg : g ∈ Γ) (v : E) (hv : v ∈ Submodule.span ℤ (Set.range b)) :
      ρ g v ∈ Submodule.span ℤ (Set.range b) := by
    rw [hb] at hv ⊢
    exact hΓ g hg v hv
  have hstable : ∀ g ∈ Γ, ∀ y ∈ L, g • y ∈ (L : Set U) := by
    intro g hg y hy
    exact MultilinearAction.Construction.integralMultilinearCoordinates_covariant_stable ρ ρ b r Λ Γ hΓb hΓ hg hy
  have hstab : multilinearOperationStabilizer b r F = stabilizer H x := by
    ext g
    change MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g F = F ↔ τ g x = x
    let e := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv (A := E) b r
    change MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g F = F ↔
      e (MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g (e.symm (e F))) = e F
    rw [e.symm_apply_apply, e.injective.eq_iff]
  change IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (multilinearOperationStabilizer b r F : Set H))
  rw [hstab]
  exact StabilizerSaturation.Construction.stabilizer_image_closed_of_discrete_invariant_set Γ x L
    (MultilinearAction.Construction.integralMultilinearCoordinates_closed b r Λ)
    (isDiscrete_iff_discreteTopology.mpr (MultilinearAction.Construction.integralMultilinearCoordinates_discrete b r Λ)) hx hstable

theorem multilinearOperationStabilizer_closed
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (r : ℕ) (F : MultilinearMap ℝ (fun _ : Fin r => E) E) :
    IsClosed (multilinearOperationStabilizer b r F : Set (Matrix.GeneralLinearGroup ι ℝ)) := by
  let H := Matrix.GeneralLinearGroup ι ℝ
  let ρ := (LatticeFrameAction.Construction.matrixFrameAction b).toMonoidHom
  let U := (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := E) b r).range
  let τ := MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ ρ b r
  let x : U := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b r F
  let : MulAction H U := MulAction.compHom U τ
  have hρ : Continuous (fun a : H × E => ρ a.1 a.2) := continuous_matrixFrameAction_joint b
  let : ContinuousSMul H U := ⟨MultilinearAction.Construction.continuous_multilinearCovariantBasisRepresentation ρ ρ b r hρ hρ⟩
  have ht : Continuous (fun g : H => g • x) := continuous_id.smul continuous_const
  have he : (multilinearOperationStabilizer b r F : Set H) = {g | τ g x = x} := by
    ext g
    change MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g F = F ↔ τ g x = x
    let e := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv (A := E) b r
    change MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g F = F ↔
      e (MultilinearAction.Construction.multilinearCovariantRepresentation ρ ρ r g (e.symm (e F))) = e F
    rw [e.symm_apply_apply, e.injective.eq_iff]
  rw [he]
  exact isClosed_eq ht continuous_const

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.TensorStabilizer.Construction
