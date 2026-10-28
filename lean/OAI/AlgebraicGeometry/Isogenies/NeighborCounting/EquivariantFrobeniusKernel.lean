import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso

/-! # Equivariant Frobenius Kernel -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel.Y

/-! The exhaustive native mixed-line kernel follows from an independent
Y kernel at any equivariantly identified Frobenius target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
  (PA PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
  (c : AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction.EquivariantAbelianIso (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian) PB.abelian
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) σ)
  (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ 1 (labels (0, false))).toGrp)
  (eB : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (0, false)) 1) q 1 1 2)
  (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (v.succ, false)) 1))

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ
local notation "τ" => labels (0, false)
local notation "ep" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q eB
local notation "eF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota hsplit k PA.abelian PB.abelian ρ σ c τ ep

abbrev targetLine (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q :=
  AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k PA.abelian ρ τ e eF J

theorem equivariant_frobenius_Y_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : PB.abelian.scheme ⟶ C) (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hg : ∀ (T : Over (Spec (.of k))) (z : T ⟶ PB.abelian.scheme), z ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit PB σ 1 (s + 1) labels
        (Fin.cases (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit PB σ τ eB
          (targetLine j iota hsplit k PA PB ρ σ c s labels e eB J)) C0) T z)
    {n : ℕ} (hn : 1 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ c.abelian.hom ≫ g)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫
          (Intrinsic.ActiveChart.nativeActiveChart j iota hsplit k PA.abelian ρ τ e).hom) ≫
            Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PA.abelian ρ hn τ) := by
  let J' := targetLine j iota hsplit k PA PB ρ σ c s labels e eB J
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit PB σ τ eB J'
  let H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (v, false)) 1) := Fin.cases H0 C0
  let ein := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ
  let hin : H0.group.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X :=
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J').hom.hom
  have : IsClosedImmersion ein.left := by
    have := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane_closed k q ep
    have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ).left :=
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed PB.abelian σ _ _
    change IsClosedImmersion ((AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom.left ≫
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ).left)
    infer_instance
  have : Mono ein := Over.mono_of_mono_left _
  have : IsClosedImmersion hin.left := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q J'
  have : Mono hin := Over.mono_of_mono_left _
  have : Mono (show (H 0).group.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X from hin) := by
    change Mono hin
    infer_instance
  have hsquare : hin ≫ ein = H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ :=
    (Category.assoc hin (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ)).symm
  have hsupport := Intrinsic.HigherChosenSupport.original_block_inclusion_supported_higher j iota hsplit PB.abelian σ
    (Nat.le_refl 1) τ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep)
  have hr := PrescribedMapKernel.prescribed_map_restricted_kernel j iota hsplit PB σ 1 (s + 1) labels H g hg
    0 ein hin hsquare (Nat.le_refl 1) hsupport
  have hp := EquivariantActiveInclusions.active_plane_ambient_source_transport j iota hsplit k AF PB.abelian ρF σ c τ ep
  have hplane : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PA.abelian ρ τ eF ≫ c.abelian.hom = ein :=
    (Category.assoc _ _ _).trans hp
  have hl := EquivariantActiveInclusions.active_line_ambient_source_transport j iota hsplit k AF PB.abelian ρF σ c τ ep J'
  have hline : ExhaustiveFrobeniusLine.transportedLine j iota hsplit k PA.abelian ρ τ e eF J ≫ c.abelian.hom =
      H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ :=
    (Category.assoc _ _ _).trans hl
  apply ExhaustiveFrobeniusLine.exhaustive_frobenius_line j iota hsplit k PA.abelian ρ τ e eF (c.abelian.hom ≫ g) J hn
  · have he : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PA.abelian ρ τ eF ≫ (c.abelian.hom ≫ g) = ein ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ g) hplane)
    exact (congrArg (fun f => AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f hin) he).mpr hr
  · intro T z hz hk
    have hz' : (z ≫ c.abelian.hom) ≫ σ.map (j.projector iota hsplit n τ) = z ≫ c.abelian.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => z ≫ f) (c.action (j.projector iota hsplit n τ)).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ c.abelian.hom) hz)))
    obtain ⟨w, hw⟩ := PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit PB σ 1 (s + 1) labels H g hg hn
      0 T (z ≫ c.abelian.hom) hz' ((Category.assoc _ _ _).trans hk)
    refine ⟨w, ?_⟩
    apply (cancel_mono c.abelian.hom).mp
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => w ≫ f) hline).trans hw)

end AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel.Y

namespace AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel.YLine

/-! The exhaustive native mixed-line kernel follows from an independent
Y kernel at any equivariantly identified Frobenius target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
  (PA PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
  (c : AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction.EquivariantAbelianIso (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian) PB.abelian
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) σ)
  (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ 1 (labels (0, false))).toGrp)
  (eB : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (0, false)) 1) q 1 1 2)
  (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (v.succ, false)) 1))

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ
local notation "τ" => labels (0, false)
local notation "ep" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q eB
local notation "eF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota hsplit k PA.abelian PB.abelian ρ σ c τ ep

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel.Y

theorem equivariant_frobenius_Y_active_kernel_of_line {C : Over (Spec (.of k))} [GrpObj C]
    (g : PB.abelian.scheme ⟶ C) (J J' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hline : J' = Y.targetLine j iota hsplit k PA PB ρ σ c s labels e eB J)
    (hg : ∀ (T : Over (Spec (.of k))) (z : T ⟶ PB.abelian.scheme), z ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit PB σ 1 (s + 1) labels
        (Fin.cases (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit PB σ τ eB J') C0) T z)
    {n : ℕ} (hn : 1 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ c.abelian.hom ≫ g)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫
          (Intrinsic.ActiveChart.nativeActiveChart j iota hsplit k PA.abelian ρ τ e).hom) ≫
            Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PA.abelian ρ hn τ) := by
  subst J'
  exact Y.equivariant_frobenius_Y_active_kernel j iota hsplit k PA PB ρ σ c s labels e eB C0 g J hg hn

end AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusKernel.YLine

end

end OAI
