import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMultiplication
import OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleUnipotentGroup
import Mathlib.Topology.Algebra.Group.Units

/-! # Unipotent Bracket Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup.Construction

noncomputable section

/-! Closed groups of bracket automorphisms and of unipotent bracket
automorphisms defined by a finite weight filtration. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L]

section Normed

variable [NormedSpace ℝ L]

theorem continuousLinearUnit_apply_inv_apply (g : (L →L[ℝ] L)ˣ) (x : L) :
    (g : L →L[ℝ] L) ((↑g⁻¹ : L →L[ℝ] L) x) = x :=
  DFunLike.congr_fun g.val_inv x

def continuousBracketUnitGroup (B : L →L[ℝ] L →L[ℝ] L) : Subgroup (L →L[ℝ] L)ˣ where
  carrier := {g | ∀ x y, (g : L →L[ℝ] L) (B x y) = B ((g : L →L[ℝ] L) x) ((g : L →L[ℝ] L) y)}
  one_mem' := fun _ _ => rfl
  mul_mem' {g h} hg hh := by
    intro x y
    change (g : L →L[ℝ] L) ((h : L →L[ℝ] L) (B x y)) = _
    rw [hh, hg]
    rfl
  inv_mem' {g} hg := by
    intro x y
    apply (ContinuousLinearEquiv.ofUnit g).injective
    change (g : L →L[ℝ] L) ((↑g⁻¹ : L →L[ℝ] L) (B x y)) =
      (g : L →L[ℝ] L) (B ((↑g⁻¹ : L →L[ℝ] L) x) ((↑g⁻¹ : L →L[ℝ] L) y))
    rw [continuousLinearUnit_apply_inv_apply, hg,
      continuousLinearUnit_apply_inv_apply, continuousLinearUnit_apply_inv_apply]

theorem continuousBracketUnitGroup_isClosed (B : L →L[ℝ] L →L[ℝ] L) :
    IsClosed (continuousBracketUnitGroup B : Set (L →L[ℝ] L)ˣ) := by
  change IsClosed {g : (L →L[ℝ] L)ˣ | ∀ x y,
    (g : L →L[ℝ] L) (B x y) = B ((g : L →L[ℝ] L) x) ((g : L →L[ℝ] L) y)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  exact isClosed_eq (Units.continuous_val.clm_apply continuous_const)
    ((B.continuous.comp (Units.continuous_val.clm_apply continuous_const)).clm_apply
      (Units.continuous_val.clm_apply continuous_const))

end Normed

variable [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def weightRaisingUnitGroup {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) :
    Subgroup (L →L[ℝ] L)ˣ :=
  NilSubmoduleUnipotentGroup.Construction.unipotentSubgroupOfNilSubmodule (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (fun X hX Y hY => Weight.RaisingMultiplication.Construction.weightRaisingOperators_mul b w X Y hX hY)
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators_isNilpotent b w)

def unipotentBracketUnitGroup {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) : Subgroup (L →L[ℝ] L)ˣ :=
  continuousBracketUnitGroup B ⊓ weightRaisingUnitGroup b w

theorem weightRaisingUnitGroup_isClosed {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) :
    IsClosed (weightRaisingUnitGroup b w : Set (L →L[ℝ] L)ˣ) := by
  have hW : IsClosed (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w : Set (L →L[ℝ] L)) :=
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w).closed_of_finiteDimensional
  exact hW.preimage (Units.continuous_val.sub continuous_const)

theorem unipotentBracketUnitGroup_isClosed {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) :
    IsClosed (unipotentBracketUnitGroup B b w : Set (L →L[ℝ] L)ˣ) :=
  (continuousBracketUnitGroup_isClosed B).inter (weightRaisingUnitGroup_isClosed b w)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup.Construction
