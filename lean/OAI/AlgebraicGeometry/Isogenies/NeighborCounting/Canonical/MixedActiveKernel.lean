import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XZActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel

/-! # Mixed Active Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedActiveKernel

noncomputable section

/-! Exhaustive active kernels of the actual Frobenius followed by the
independent canonical Y or Z quotient. The canonical normalized Cartier
pairing is retained in every opposite block of each input full kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine.Plane OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)

variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (compact : Fin s → Bool)
variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 (labels (0, false))).toGrp)
variable (eF : ∀ (m : ℕ) (v : Fin (s + 1)), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v, false)) m) q m
      (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (C0 : ∀ (m : ℕ) (v : Fin s), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v.succ, false)) m))

theorem canonical_XY_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme ⟶ C) (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hkernel : ∀ (T : Over (Spec (.of k)))
      (a : T ⟶ (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme), a ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) 1 (s + 1) labels
        (Fin.cases
          (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
            (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (0, false)) (eF 1 0)
            (Intrinsic.XYActiveKernel.targetLineIndex j iota hsplit k PEL ρ s labels compact e eF L)) (C0 1)) T a)
    {n : ℕ} (hn : 1 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (0, false)))) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom) ≫
          (Intrinsic.ActiveChart.nativeActiveChart j iota hsplit k PEL.abelian ρ (labels (0, false)) e).hom) ≫
            Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PEL.abelian ρ hn (labels (0, false))) := by
  let τ := labels (0, false)
  let σ := AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ
  let ep := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (eF 1 0)
  let L' := Intrinsic.XYActiveKernel.targetLineIndex j iota hsplit k PEL ρ s labels compact e eF L
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ τ (eF 1 0) L'
  let H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ (labels (v, false)) 1) :=
    Fin.cases H0 (C0 1)
  let ein := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 1 τ
  let h : H0.group.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X :=
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L').hom.hom
  have : IsClosedImmersion ein.left := by
    have := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane_closed k q ep
    have : IsClosedImmersion
        (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 1 τ).left :=
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ _ _
    change IsClosedImmersion ((AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom.left ≫
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 1 τ).left)
    infer_instance
  have : Mono ein := Over.mono_of_mono_left _
  have : IsClosedImmersion h.left := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q L'
  have : Mono h := Over.mono_of_mono_left _
  have : Mono (show (H 0).group.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X from h) := by
    change Mono h
    infer_instance
  have hsquare : h ≫ ein = H0.inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 1 τ :=
    (Category.assoc h (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 1 τ)).symm
  have hsupport := Intrinsic.HigherChosenSupport.original_block_inclusion_supported_higher j iota hsplit
    (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ (Nat.le_refl 1) τ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep)
  have hr := PrescribedMapKernel.prescribed_map_restricted_kernel j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ 1 (s + 1)
    labels H g hkernel 0 ein h hsquare (Nat.le_refl 1) hsupport
  apply ExhaustiveFrobeniusLine.exhaustive_frobenius_line j iota hsplit k PEL.abelian ρ τ e ep g L hn hr
  intro T a ha hk
  exact PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ 1 (s + 1)
    labels H g hkernel hn 0 T a ha hk

include e in
theorem canonical_XZ_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme ⟶ C)
    (hkernel : ∀ (T : Over (Spec (.of k)))
      (a : T ⟶ (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme), a ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) 2 (s + 1) labels
        (Fin.cases
          (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
            (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (0, false)) (eF 1 0))
          (C0 2)) T a)
    {n : ℕ} (hn : 2 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (0, false)))) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g)
      (Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PEL.abelian ρ
        (Nat.le_trans (show 1 ≤ 2 by decide) hn) (labels (0, false))) := by
  let τ := labels (0, false)
  let σ := AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ
  let ep := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (eF 1 0)
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ τ (eF 1 0)
  let H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ (labels (v, false)) 2) :=
    Fin.cases H0 (C0 2)
  let i := H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian σ 2 τ
  have hi : i = PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PEL.abelian ρ τ ep :=
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_inclusion j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ τ (eF 1 0)
  have hz := PrescribedMapKernel.prescribed_map_chosen_killed j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ 2 (s + 1)
    labels H g hkernel 0 H0.group.X (𝟙 _)
  have hg : i ≫ g = 1 := (congrArg (fun z => z ≫ g) (Category.id_comp i)).symm.trans hz
  have hplane : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PEL.abelian ρ τ ep ≫ g = 1 :=
    (congrArg (fun z => z ≫ g) hi.symm).trans hg
  apply ExhaustiveFrobeniusLine.Plane.exhaustive_frobenius_plane j iota hsplit k PEL.abelian ρ τ e ep g
    (Nat.le_trans (show 1 ≤ 2 by decide) hn) hplane
  intro T a ha hk
  obtain ⟨b, hb⟩ := PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL) σ 2 (s + 1)
    labels H g hkernel hn 0 T a ha hk
  exact ⟨b, (congrArg (fun z => b ≫ z) hi).symm.trans hb⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedActiveKernel
