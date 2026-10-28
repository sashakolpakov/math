import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitCompletion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionBlockSubgroups

/-! # Points Tate Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction

noncomputable section

/-!
The completed source actions and Tate blocks are constructed directly
from the CMPoints residue coordinates. Their finite-level points are the
actual native torsion-block points, through the same abelian-scheme point.
No candidate correspondence or IsogenyQuotient realization is input to this construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionBlockSubgroups

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N : ℕ} (T : Over S)
  (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)

def l45SplitTateAction : (Gal(E/ℚ) → ℤ_[q]) →ₐ[ℤ_[q]]
    Module.End ℤ_[q] (TateComparison.Add.schemeTateModule F.abelian.scheme T q) :=
  (TateComparison.TateAction.tateCompletedAction T q F).comp (SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm.toAlgHom

def l45SplitTorsionAction (n : ℕ) : (Gal(E/ℚ) → ℤ_[q]) →ₐ[ℤ_[q]]
    Module.End ℤ_[q] (TateComparison.Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  (TateComparison.TorsionAction.torsionCompletedAction T q n F).comp (SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm.toAlgHom

def l45IntegralTateBlock (τ : Gal(E/ℚ)) :
    Submodule ℤ_[q] (TateComparison.Add.schemeTateModule F.abelian.scheme T q) :=
  TateComparison.ProductActionDecomposition.ProductAction.block (l45SplitTateAction j iota hsplit T F) τ

def l45FiniteTateBlock (n : ℕ) (τ : Gal(E/ℚ)) :
    Submodule ℤ_[q] (TateComparison.Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  TateComparison.ProductActionDecomposition.ProductAction.block (l45SplitTorsionAction j iota hsplit T F n) τ

theorem l45Evaluate_splitAction (n : ℕ) (a : Gal(E/ℚ) → ℤ_[q]) :
    (TateComparison.Evaluation.Tate.evaluate q n).comp (l45SplitTateAction j iota hsplit T F a) =
      (l45SplitTorsionAction j iota hsplit T F n a).comp (TateComparison.Evaluation.Tate.evaluate q n) :=
  TateComparison.TorsionAction.evaluate_completedAction T q n F ((SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm a)

def l45EvaluateBlock (n : ℕ) (τ : Gal(E/ℚ)) :
    l45IntegralTateBlock j iota hsplit T F τ →ₗ[ℤ_[q]] l45FiniteTateBlock j iota hsplit T F n τ :=
  TateComparison.ProductActionDecomposition.ProductAction.blockMap (l45SplitTateAction j iota hsplit T F)
    (l45SplitTorsionAction j iota hsplit T F n) (TateComparison.Evaluation.Tate.evaluate q n)
    (l45Evaluate_splitAction j iota hsplit T F n) τ

theorem l45SplitTorsionAction_integer (n : ℕ) (a : NumberField.RingOfIntegers E) :
    l45SplitTorsionAction j iota hsplit T F n (fun τ => j.localCharacter iota τ a) =
      TateComparison.TorsionAction.torsionIntegralAction T q n F a := by
  rw [← SplitCompletion.Construction.l45CompletionMap_integer j iota a]
  change TateComparison.TorsionAction.torsionCompletedAction T q n F
    ((SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm ((SplitCompletion.Construction.l45CompletionEquiv j iota hsplit) (1 ⊗ₜ[ℤ] a))) = _
  rw [AlgEquiv.symm_apply_apply, TateComparison.TorsionAction.torsionCompletedAction_tmul, one_smul]

omit [IsGalois ℚ E] in
include hsplit in
theorem l45SplitBlock_mem_iff_characters
    {V : Type*} [AddCommGroup V] [Module ℤ_[q] V]
    (θ : (Gal(E/ℚ) → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] V)
    (τ : Gal(E/ℚ)) (x : V) :
    x ∈ TateComparison.ProductActionDecomposition.ProductAction.block θ τ ↔ ∀ a : NumberField.RingOfIntegers E,
      θ (fun υ => j.localCharacter iota υ a) x = j.localCharacter iota τ a • x := by
  rw [TateComparison.ProductActionDecomposition.ProductAction.mem_block_iff]
  constructor
  · intro hx a
    exact hx (fun υ => j.localCharacter iota υ a)
  · intro hx a
    have he (z : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
        θ (SplitCompletion.Construction.l45CompletionMap j iota z) x = SplitCompletion.Construction.l45CompletionMap j iota z τ • x := by
      induction z using TensorProduct.inductionOn with
      | tmul b r =>
        change θ (b • (fun υ => j.localCharacter iota υ r)) x =
          (b • (fun υ => j.localCharacter iota υ r)) τ • x
        rw [map_smul, LinearMap.smul_apply, hx r]
        exact smul_smul b (j.localCharacter iota τ r) x
      | add z z' hz hz' =>
        rw [map_add, map_add, LinearMap.add_apply, Pi.add_apply, add_smul, hz, hz']
    obtain ⟨z, hz⟩ := SplitCompletion.Construction.l45CompletionMap_surjective j iota hsplit a
    rw [← hz]
    exact he z

theorem l45FiniteTateBlock_mem_iff (n : ℕ) (τ : Gal(E/ℚ))
    (x : TateComparison.Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :
    x ∈ l45FiniteTateBlock j iota hsplit T F n τ ↔
      x.val.toMul ∈ PELModuli.CMPoints.BlocksProjectors.blockPoints F.abelian (TateComparison.PELAdapters.actionFromEnd F.action) (j.localCharacter iota τ) n T := by
  change x ∈ TateComparison.ProductActionDecomposition.ProductAction.block (l45SplitTorsionAction j iota hsplit T F n) τ ↔ _
  rw [l45SplitBlock_mem_iff_characters j iota hsplit]
  simp_rw [l45SplitTorsionAction_integer]
  have hp : x.val.toMul ^ (q ^ n) = 1 := by
    have hx := congrArg Additive.toMul x.property
    simpa using hx
  constructor
  · intro hx
    refine ⟨hp, ?_⟩
    intro a
    have he := congrArg (fun y : TateComparison.Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n => y.val.toMul) (hx a)
    rw [TateComparison.TorsionBlockSubgroups.torsionIntegralAction_point, TateComparison.TorsionBlockSubgroups.Tate.padic_smul_val, toMul_nsmul] at he
    exact he
  · intro hx a
    apply Subtype.ext
    apply Additive.toMul.injective
    rw [TateComparison.TorsionBlockSubgroups.torsionIntegralAction_point, TateComparison.TorsionBlockSubgroups.Tate.padic_smul_val, toMul_nsmul]
    exact hx.2 a

def l45FiniteTateBlockPointsEquiv (n : ℕ) (τ : Gal(E/ℚ)) :
    l45FiniteTateBlock j iota hsplit T F n τ ≃+
      Additive (PELModuli.CMPoints.BlocksProjectors.blockPoints F.abelian (TateComparison.PELAdapters.actionFromEnd F.action) (j.localCharacter iota τ) n T) where
  toFun x := Additive.ofMul ⟨x.val.val.toMul, (l45FiniteTateBlock_mem_iff j iota hsplit T F n τ x.val).mp x.property⟩
  invFun y := by
    let z : TateComparison.Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n :=
      ⟨Additive.ofMul y.toMul.val, by
        apply Additive.toMul.injective
        rw [toMul_nsmul]
        exact y.toMul.property.1⟩
    exact ⟨z, (l45FiniteTateBlock_mem_iff j iota hsplit T F n τ z).mpr y.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def l45TateNativeBlockEquiv (n : ℕ) (τ : Gal(E/ℚ)) :
    l45FiniteTateBlock j iota hsplit T F n τ ≃+
      Additive (T ⟶ OppositeKernel.Construction.torsionBlock (q ^ n) ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ))) :=
  (l45FiniteTateBlockPointsEquiv j iota hsplit T F n τ).trans
    (PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit F.abelian (TateComparison.PELAdapters.actionFromEnd F.action) n τ T).toAdditive.symm

theorem l45TateNativeBlockEquiv_inclusion (n : ℕ) (τ : Gal(E/ℚ))
    (x : l45FiniteTateBlock j iota hsplit T F n τ) :
    (l45TateNativeBlockEquiv j iota hsplit T F n τ x).toMul ≫
      OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) =
        x.val.val.toMul :=
  congrArg Subtype.val
    ((PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit F.abelian (TateComparison.PELAdapters.actionFromEnd F.action) n τ T).apply_symm_apply
      (l45FiniteTateBlockPointsEquiv j iota hsplit T F n τ x).toMul)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks.Construction
