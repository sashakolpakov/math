import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-! # Points Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoices.Construction

noncomputable section

/-!
The actual CMPoints coordinates identify geometric supported choices with
raw rank-three cosets. The completed action is constructed from CMPoints;
TorsionQuotient supplies finite-etale geometry and geometric division. The exact
membership formula uses the original subgroup and actual Tate evaluation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E L K : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] [Field K] [CharZero K]
  {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N : ℕ} (base : S ⟶ Spec (.of K))
  (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (n : ℕ) (τ : Gal(E/ℚ)) (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]

def l45SupportedTateChoices :
    SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) (Over.mk b) ≃
      {J : AddSubgroup (PointsTateBlocks.Construction.l45FiniteTateBlock j iota hsplit (Over.mk b) F n τ) // Nonempty (J ≃+ M)} := by
  let p := (TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)
  have hg := OppositeKernel.Construction.torsionBlock_finite_etale (q ^ n) p
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient base (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) Torsion.Construction.verified_TorsionQuotientInput)
  have : IsFinite (OppositeKernel.Construction.torsionBlock (q ^ n) p).hom := hg.1
  have : Etale (OppositeKernel.Construction.torsionBlock (q ^ n) p).hom := hg.2
  exact Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ n) M k b p
    (PointsTateBlocks.Construction.l45TateNativeBlockEquiv j iota hsplit (Over.mk b) F n τ)

theorem l45SupportedTateChoices_membership
    (H : SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) (Over.mk b))
    (x : PointsTateBlocks.Construction.l45FiniteTateBlock j iota hsplit (Over.mk b) F n τ) :
    x ∈ (l45SupportedTateChoices j iota hsplit base F n τ k b M H).val ↔
      x.val.val.toMul ∈ H.val.subgroup.points (Over.mk b) (𝟙 _) := by
  unfold l45SupportedTateChoices
  rw [Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv_membership, PointsTateBlocks.Construction.l45TateNativeBlockEquiv_inclusion]

variable (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ n) (hdominant : Antitone a)
  (basis : Module.Basis (Fin 3) ℤ_[q] (PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk b) F τ))

def l45RawTateChoices :
    Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) ≃
      {J : AddSubgroup (PointsTateBlocks.Construction.l45FiniteTateBlock j iota hsplit (Over.mk b) F n τ) //
        Nonempty (J ≃+ (∀ i, ZMod (q ^ a i)))} :=
  BlockTateChoices.Construction.rawTateBlockSubgroupChoicesEquiv q n (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit (Over.mk b) F)
    (PointsTateBlocks.Construction.l45SplitTorsionAction j iota hsplit (Over.mk b) F n)
    (PointsTateBlocks.Construction.l45Evaluate_splitAction j iota hsplit (Over.mk b) F n)
    (Geometric.TateKernel.Construction.geometricPoint_q_divisible_from_TorsionQuotient base F.abelian b q Fact.out Torsion.Construction.verified_TorsionQuotientInput)
    τ basis a ha hdominant ElementaryDivisors.Construction.verified_ElementaryDivisorsInput

variable (eM : M ≃+ (∀ i, ZMod (q ^ a i)))

def l45SupportedRawChoices :
    SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) (Over.mk b) ≃
      Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) :=
  ((l45SupportedTateChoices j iota hsplit base F n τ k b M).trans
    (Geometric.TateChoices.Construction.typedAdditiveTargetEquiv eM)).trans
      (l45RawTateChoices j iota hsplit base F n τ k b a ha hdominant basis).symm

theorem l45SupportedRawChoices_subgroup
    (H : SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) (Over.mk b)) :
    (l45RawTateChoices j iota hsplit base F n τ k b a ha hdominant basis
      (l45SupportedRawChoices j iota hsplit base F n τ k b M a ha hdominant basis eM H)).val =
        (l45SupportedTateChoices j iota hsplit base F n τ k b M H).val := by
  change ((l45RawTateChoices j iota hsplit base F n τ k b a ha hdominant basis)
    ((l45RawTateChoices j iota hsplit base F n τ k b a ha hdominant basis).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem l45SupportedRawChoices_membership
    (H : SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ)) (Over.mk b))
    (x : PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk b) F τ) :
    (PointsTateBlocks.Construction.l45EvaluateBlock j iota hsplit (Over.mk b) F n τ x).val.val.toMul ∈
        H.val.subgroup.points (Over.mk b) (𝟙 _) ↔
      (TateChoices.Construction.standardBoundedLatticeResidues q n).symm (IsogenyQuotient.Basis.Construction.basisCoordinateResidues q basis (fun _ => n) x) ∈
        (BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q n a ha hdominant ElementaryDivisors.Construction.verified_ElementaryDivisorsInput
          (l45SupportedRawChoices j iota hsplit base F n τ k b M a ha hdominant basis eM H)).val := by
  rw [← l45SupportedTateChoices_membership j iota hsplit base F n τ k b M H,
    ← l45SupportedRawChoices_subgroup j iota hsplit base F n τ k b M a ha hdominant basis eM H]
  exact BlockTateChoices.Construction.rawTateBlockSubgroupChoicesEquiv_membership q n
    (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit (Over.mk b) F)
    (PointsTateBlocks.Construction.l45SplitTorsionAction j iota hsplit (Over.mk b) F n)
    (PointsTateBlocks.Construction.l45Evaluate_splitAction j iota hsplit (Over.mk b) F n)
    (Geometric.TateKernel.Construction.geometricPoint_q_divisible_from_TorsionQuotient base F.abelian b q Fact.out Torsion.Construction.verified_TorsionQuotientInput)
    τ basis a ha hdominant ElementaryDivisors.Construction.verified_ElementaryDivisorsInput _ x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoices.Construction
