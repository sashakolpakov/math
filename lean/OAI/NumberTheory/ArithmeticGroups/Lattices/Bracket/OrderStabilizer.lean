import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.TransportGroupEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketLattice

/-! # Order Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrderStabilizer.Construction

noncomputable section

/-! Integral bracket automorphisms described without a choice of coordinates. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]

def bracketIntegralAction (B : L →L[ℝ] L →L[ℝ] L) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →* (L ≃ₗ[ℤ] L) where
  toFun g := (ContinuousLinearEquiv.ofUnit g.val).toLinearEquiv.restrictScalars ℤ
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

def bracketOrderStabilizer (B : L →L[ℝ] L →L[ℝ] L) (Λ : Submodule ℤ L) :
    Subgroup (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) := SubmoduleOrbit.Construction.submoduleImageStabilizer (bracketIntegralAction B) Λ

theorem mem_bracketOrderStabilizer_iff (B : L →L[ℝ] L →L[ℝ] L) (Λ : Submodule ℤ L)
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    g ∈ bracketOrderStabilizer B Λ ↔ ∀ x, g.val.val x ∈ Λ ↔ x ∈ Λ :=
  StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (bracketIntegralAction B) Λ g

theorem bracketOrderStabilizer_transport
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : L ≃L[ℝ] V) (B : L →L[ℝ] L →L[ℝ] L) (Λ : Submodule ℤ L) :
    (bracketOrderStabilizer (Positive.Killing.Construction.continuousBracketTransport e B)
      (Λ.map (e.toLinearMap.restrictScalars ℤ))).comap (TransportGroupEquiv.Construction.bracketTransportGroupEquiv e B).toMonoidHom =
      bracketOrderStabilizer B Λ := by
  have hm (x : L) : e x ∈ Λ.map (e.toLinearMap.restrictScalars ℤ) ↔ x ∈ Λ := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext g
  change TransportGroupEquiv.Construction.bracketTransportGroupEquiv e B g ∈ bracketOrderStabilizer _ _ ↔ _
  rw [mem_bracketOrderStabilizer_iff, mem_bracketOrderStabilizer_iff]
  constructor
  · intro h x
    have he := h (e x)
    change e (g.val.val (e.symm (e x))) ∈ _ ↔ e x ∈ _ at he
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hm] using he
  · intro h x
    obtain ⟨y, rfl⟩ := e.surjective x
    change e (g.val.val (e.symm (e y))) ∈ _ ↔ e y ∈ _
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hm] using h y

theorem integralBracketSubgroup_eq_orderStabilizer
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ V) (B : V →L[ℝ] V →L[ℝ] V)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    Integral.BracketLattice.Construction.integralBracketSubgroup b B hK = bracketOrderStabilizer B (Submodule.span ℤ (Set.range b)) := by
  ext g
  change VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b (ConjugationAction.Construction.bracketVolumeHom B hK g) ∈
    SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b.toBasis) _ ↔ _
  rw [StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff, mem_bracketOrderStabilizer_iff]
  exact forall_congr' (fun x => by
    change (LatticeFrameAction.Construction.matrixFrameAction b.toBasis (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b (ConjugationAction.Construction.bracketVolumeHom B hK g)) x ∈ _ ↔ _) ↔ _
    rw [Integral.OperatorBracketStability.Construction.matrixFrameAction_volumeOperator]
    rfl)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrderStabilizer.Construction
