import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusMixedKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties

/-! # Exhaustive Frobenius Line -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine

/-! The original abelian Frobenius followed by a one-step etale-line
quotient has the computed active kernel in every higher coefficient
block. The complementary Verschiebung excludes additional higher
torsion sections; the actual line permutation is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusMixedKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "F" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k A

variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (eF : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

abbrev sourceLine (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ

abbrev transportedLine (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q eF (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A)
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ

omit [IsAlgClosed k] [CharP k q] in
theorem sourceLine_killed (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    sourceLine j iota hsplit k A ρ τ e L ^ q = 1 := by
  have hp := (Intrinsic.ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit A ρ 1 τ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L)).1
  have h := hp (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X (toUnit _) _
    ⟨𝟙 _, by
      change (𝟙 _) ≫ (sourceLine j iota hsplit k A ρ τ e L) = _
      exact Category.id_comp _⟩
  simpa only [pow_one] using h

theorem exhaustive_frobenius_line {C : Over (Spec (.of k))} [GrpObj C]
    (g : (AF).scheme ⟶ C) (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) {n : ℕ} (hn : 1 ≤ n)
    (hsecond : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k A ρ τ eF ≫ g)
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q
        (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom)
    (hfactor : ∀ (T : Over (Spec (.of k))) (a : T ⟶ (AF).scheme),
      a ≫ (ρF).map (j.projector iota hsplit n τ) = a → a ≫ g = 1 →
        ∃ h, h ≫ transportedLine j iota hsplit k A ρ τ e eF L = a) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ (F).hom ≫ g)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom) ≫
          (Intrinsic.ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e).hom) ≫
            Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) := by
  have hl := Intrinsic.ActiveChart.native_qblock_kernel_of_chart j iota hsplit k A ρ τ e ((F).hom ≫ g)
    (𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom)
    (PointsFrobeniusMixedLine.CM.native_frobenius_mixed_line j iota hsplit k A ρ τ e eF g L hsecond)
  exact Intrinsic.FrobeniusMixedKernel.native_frobenius_kernel_from_qblock j iota hsplit A ρ hn τ
    (sourceLine j iota hsplit k A ρ τ e L)
    (transportedLine j iota hsplit k A ρ τ e eF L)
    ((Grp.forget _).mapIso (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineIso j iota hsplit k A ρ τ e eF L))
    (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineIso_abelian j iota hsplit k A ρ τ e eF L)
    (sourceLine_killed j iota hsplit k A ρ τ e L) g hfactor _ hl

end AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine

namespace AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine.Plane

/-! If the second one-step active kernel is the original etale q-plane,
the mixed active kernel is the entire original q-block. Verschiebung
proves that there are no additional sections in higher torsion blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusMixedKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))
variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (eF : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "F" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k A

abbrev sourcePlane := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ

omit [IsAlgClosed k] [CharP k q] in
theorem sourcePlane_killed : sourcePlane j iota hsplit k A ρ τ e ^ q = 1 := by
  have hp := (Intrinsic.ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit A ρ 1 τ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e)).1
  have h := hp (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X (toUnit _) _
    ⟨𝟙 _, by
      change (𝟙 _) ≫ sourcePlane j iota hsplit k A ρ τ e = _
      exact Category.id_comp _⟩
  simpa only [pow_one] using h

theorem native_plane_transport :
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF).hom.hom.hom ≫
      PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k A ρ τ eF = sourcePlane j iota hsplit k A ρ τ e ≫ (F).hom := by
  have h := (PointsFrobeniusMixedLine.CM.native_frobenius_plane_square j iota hsplit k A ρ τ e eF).symm
  have hs : (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom = MixedKernels.etaleInclusion ≫ e.inv.hom.hom := rfl
  simpa only [MixedKernels.etaleImage, PointsFrobeniusMixedLine.CM.activeChart, sourcePlane, hs, Category.assoc] using h

include e in
theorem exhaustive_frobenius_plane {C : Over (Spec (.of k))} [GrpObj C]
    (g : (AF).scheme ⟶ C) {n : ℕ} (hn : 1 ≤ n)
    (hsecond : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k A ρ τ eF ≫ g = 1)
    (hfactor : ∀ (T : Over (Spec (.of k))) (a : T ⟶ (AF).scheme),
      a ≫ (ρF).map (j.projector iota hsplit n τ) = a → a ≫ g = 1 →
        ∃ h, h ≫ PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k A ρ τ eF = a) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ (F).hom ≫ g)
      (Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) := by
  have hp := MixedKernels.quotient_restricts_to_etale_projection (PointsFrobeniusMixedLine.CM.activeChart j iota hsplit k A ρ τ e) (F).hom
    (PointsFrobeniusMixedLine.CM.native_frobenius_kills_multiplicative j iota hsplit k A ρ τ e)
  have hz : PointsFrobeniusMixedLine.CM.activeChart j iota hsplit k A ρ τ e ≫ (F).hom ≫ g = 1 := by
    have h := congrArg (fun z => z ≫ g) hp
    simpa only [Category.assoc, PointsFrobeniusMixedLine.CM.native_frobenius_plane_square j iota hsplit k A ρ τ e eF,
      hsecond, MonObj.comp_one] using h
  let c := Intrinsic.ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e
  let f := (F).hom ≫ g
  have hc : c.inv ≫ (PointsFrobeniusMixedLine.CM.activeChart j iota hsplit k A ρ τ e ≫ f) =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) ≫ f :=
    (Category.assoc c.inv (PointsFrobeniusMixedLine.CM.activeChart j iota hsplit k A ρ τ e) f).symm.trans
      (congrArg (fun z => z ≫ f) (Intrinsic.ActiveChart.nativeActiveChart_inv_inclusion j iota hsplit k A ρ τ e))
  have hzero : AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) ≫ f = 1 :=
    hc.symm.trans ((congrArg (fun z => c.inv ≫ z) hz).trans (MonObj.comp_one c.inv))
  have hu : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) ≫ f) (𝟙 _) := by
    intro T a
    constructor
    · intro _
      exact ⟨a, Category.comp_id _, fun b hb => (Category.comp_id b).symm.trans hb⟩
    · intro _
      rw [hzero, MonObj.comp_one]
  have hh := Intrinsic.FrobeniusMixedKernel.native_frobenius_kernel_from_qblock j iota hsplit A ρ hn τ
    (sourcePlane j iota hsplit k A ρ τ e) (PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k A ρ τ eF)
    ((Grp.forget _).mapIso (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF))
    (native_plane_transport j iota hsplit k A ρ τ e eF)
    (sourcePlane_killed j iota hsplit k A ρ τ e) g hfactor (𝟙 _) hu
  change AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ (F).hom ≫ g)
    ((𝟙 (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)))) ≫
      Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) at hh
  simpa only [Category.id_comp] using hh

end AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine.Plane

end

end OAI
