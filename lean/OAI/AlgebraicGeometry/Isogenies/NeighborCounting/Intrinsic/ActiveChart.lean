import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Active Chart -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart

noncomputable section

/-! The ordinary product chart identifies the original active block
with IsogenyQuotient's native coefficient q-torsion, retaining the ambient
inclusion. Kernel calculations transport through this constructed chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))
variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)

def nativeActiveChart :
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X ≅
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) :=
  ((Grp.forget _).mapIso e).symm ≪≫
    ((Grp.forget _).mapIso
      (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit A ρ 1 τ)).symm

theorem nativeActiveChart_inclusion :
    (nativeActiveChart j iota hsplit k A ρ τ e).hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) =
        e.inv.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ := by
  let c := (Grp.forget _).mapIso
    (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit A ρ 1 τ)
  have hc : c.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) :=
    CMPointsBlockComparison.nativeCMPointsBlockGroupIso_inclusion j iota hsplit A ρ 1 τ
  have hi : c.inv ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) =
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ := by
    exact (congrArg (fun z => c.inv ≫ z) hc.symm).trans
      (c.inv_hom_id_assoc (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ))
  change (e.inv.hom.hom ≫ c.inv) ≫
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) = _
  exact (Category.assoc e.inv.hom.hom c.inv
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)))).trans
      (congrArg (fun z => e.inv.hom.hom ≫ z) hi)

theorem nativeActiveChart_inv_inclusion :
    (nativeActiveChart j iota hsplit k A ρ τ e).inv ≫
      (e.inv.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) := by
  exact (congrArg (fun z => (nativeActiveChart j iota hsplit k A ρ τ e).inv ≫ z)
    (nativeActiveChart_inclusion j iota hsplit k A ρ τ e).symm).trans
      ((nativeActiveChart j iota hsplit k A ρ τ e).inv_hom_id_assoc _)

theorem native_qblock_kernel_of_chart {H C : Over (Spec (.of k))} [GrpObj C]
    (f : A.scheme ⟶ C)
    (u : H ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X)
    (hu : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel ((e.inv.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ≫ f) u) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) ≫ f)
      (u ≫ (nativeActiveChart j iota hsplit k A ρ τ e).hom) := by
  apply MixedKernelExhaustion.prescribedKernel_of_kernel_factors _ (nativeActiveChart j iota hsplit k A ρ τ e).hom u
  · rw [← Category.assoc, nativeActiveChart_inclusion]
    exact hu
  · intro T a _
    exact ⟨a ≫ (nativeActiveChart j iota hsplit k A ρ τ e).inv, by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
