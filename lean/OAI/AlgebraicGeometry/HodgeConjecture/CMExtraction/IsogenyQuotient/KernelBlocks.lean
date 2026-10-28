import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # Kernel Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.KernelBlocks

noncomputable section

/-! The complete native chosen/opposite kernel determines each TateComparison chosen
block on all tests. Orthogonality and the original CMPoints characters supply
the intersection calculation; no block-kernel equation is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E L K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} [Field K] [CharZero K]
  {q s g N : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (base : S ⟶ Spec (.of K)) (Q : Over S)
  (h : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (a : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ h)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

variable {W : Over S} [GrpObj W]
  (ep : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ h) ((AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) v))
    (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ h) ((AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) v)) (W := W))
  (U₀ : ∀ v, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ h) ((fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) v) ((AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) v) Q)

variable (model : ((AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀)).Model) {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Q.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (F.abelian.pullback Q.hom) B)
  (hker : ∀ (U : Over Q.left) (z : U ⟶ (F.abelian.pullback Q.hom).scheme),
    z ≫ f.hom = 1 ↔ ∃! w : U ⟶ (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀) model).X,
      w ≫ AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion F.abelian Q (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀) model = z)

include hker in
theorem fullKernel_chosen_block (v : Fin s) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (F.pullback Q.hom) (j.localCharacter iota (labels (.inl v))) h) =
      (HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F base Q h
        (fun v => labels (.inl v)) a U₀).val v := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext z
  let e := F.abelian.baseChangePointsMulEquiv Q.hom T
  have hq : z ≫ f.hom = 1 ↔ e z ∈ ((AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀)).points
      ((Over.map Q.hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q T) :=
    AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints.Construction.nativeQuotient_kernel_membership F.abelian Q (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀) model f hker T z
  have hc (hz : z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock (F.pullback Q.hom)
      (j.localCharacter iota (labels (.inl v))) h).atTest T) :
      e z ∈ ((AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (A := F.abelian.scheme) (P := Q) (W := W) (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀)).points ((Over.map Q.hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q T) ↔
      e z ∈ (U₀ v).val.subgroup.points ((Over.map Q.hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q T) := by
    have hb : e z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock F (j.localCharacter iota (labels (.inl v))) h).atTest
        ((Over.map Q.hom).obj T) := by
      rw [← AbelianScheme.TateComparison.SplitSubgroups.splitBlock_pullback] at hz
      exact hz
    have hf := ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit F.abelian
      (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h (labels (.inl v)) ((Over.map Q.hom).obj T) (e z)).mp hb).2
    exact AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection.Construction.choiceFullKernel_chosen_membership (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit F.abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels) ep U₀
      (fun w t hwt => AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy.Construction.l45_choice_torsion_orthogonal j iota hsplit F.abelian
        (AbelianScheme.TateComparison.PELAdapters.actionFromEnd F.action) h s labels t w hwt.symm)
      ((Over.map Q.hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q T) v (e z) hf
  have hp := HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv_membership j iota hsplit F base Q h
    (fun v => labels (.inl v)) a U₀ v T z
  change (z ≫ f.hom = 1 ∧ z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock (F.pullback Q.hom)
    (j.localCharacter iota (labels (.inl v))) h).atTest T) ↔ _
  constructor
  · intro hz
    exact hp.mpr ((hc hz.2).mp (hq.mp hz.1))
  · intro hz
    have hb := (HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F base Q h
      (fun v => labels (.inl v)) a U₀).property v |>.2.1 T hz
    exact ⟨hq.mpr ((hc hb).mpr (hp.mp hz)), hb⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.KernelBlocks
