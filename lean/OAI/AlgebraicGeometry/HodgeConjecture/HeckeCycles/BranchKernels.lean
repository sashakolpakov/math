import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReducedReferencePoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel

/-! # Branch Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchKernels.CM

noncomputable section

/-! The original and retained correspondences have the same chosen
kernel at each matched branch, through their actual PEL comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel.IsogenyQuotient
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM.Restricted

variable {R : Type} [CommRing R] {g N n q : ℕ} [Fact q.Prime]
  {B B' : Scheme.{0}} (p : B' ⟶ B) (M : Over B) {X : Over B'}
  [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M))
  (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N M.left) (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X.left)
  (eA : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e)))
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M)
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (U.pullback C.source.left) (U.pullback C.target.left) n)

def isogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left)
      (A.pullback (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).target.left) n :=
  CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictPELIsogeny A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C)
    C.source.left C.target.left (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left
    (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).target.left
    (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source p M e C) (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_target p M e C) f

variable (χ : R →+* ℤ_[q]) (h : ℕ)

def originalKernel : AbelianScheme.TateComparison.Subgroups.PointSubgroup (U.pullback C.source.left).abelian :=
  (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback C.source.left) χ h)

def kernel : AbelianScheme.TateComparison.Subgroups.PointSubgroup (A.pullback (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left).abelian :=
  (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (CM.isogeny p M e U A eA C f).isogeny.hom).inf
    (AbelianScheme.TateComparison.Subgroups.splitBlock (A.pullback (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left) χ h)

theorem kernel_eq :
    kernel p M e U A eA C f χ h =
      ((originalKernel M U C f χ h).pullback (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C)).comapHom
        (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA
          (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C) C.source.left (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left
          (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source p M e C)).abelian.hom :=
  CMExtraction.PEL.RestrictionKernel.IsogenyQuotient.restrictPELIsogeny_splitKernel A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C)
    C.source.left C.target.left (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left
    (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).target.left
    (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source p M e C) (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_target p M e C) f χ h

theorem geometry (a : Fin 3 → ℕ)
    (hfin : (originalKernel M U C f χ h).HasFiniteEtaleModel)
    (htype : (originalKernel M U C f χ h).HasGeometricType q a) :
    (kernel p M e U A eA C f χ h).HasFiniteEtaleModel ∧
      (kernel p M e U A eA C f χ h).HasGeometricType q a := by
  rw [kernel_eq]
  exact ⟨AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso _
      (AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_pullback _ hfin _) _,
    AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_comapIso _
      (AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_pullback _ htype _) _⟩

variable {T : Over B'} (x : T ⟶ X) (c : (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x)

theorem at_branch :
    KernelAtLiftEquality.CM.Restricted.atLift A (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left (kernel p M e U A eA C f χ h)
      x.left c.val.left (congrArg (fun z => z.left) c.property) =
    (KernelAtLiftEquality.CM.Restricted.atLift U C.source.left (originalKernel M U C f χ h)
      (x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e)
      (ReducedReferencePoint.CM.Reference.branchEquiv p M e x C c).val.left
      (congrArg (fun z => z.left) (ReducedReferencePoint.CM.Reference.branchEquiv p M e x C c).property)).comapHom
        (PELRestrictionNaturality.CM.atPoint A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA x.left).abelian.hom := by
  have hc : (c.val.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C) ≫ C.source.left =
      x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e := by
    rw [Category.assoc, CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source, ← Category.assoc]
    exact congrArg (fun z => z.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) c.property
  rw [kernel_eq]
  have hr := KernelAtLiftEquality.CM.Restricted.restrict_atLift A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C)
    C.source.left (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source p M e C)
    (originalKernel M U C f χ h) c.val.left x.left (congrArg (fun z => z.left) c.property) hc
  have hb := KernelAtLiftEquality.CM.branch_congr U C.source.left (originalKernel M U C f χ h)
    (x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e)
    (ReducedReferencePoint.CM.Reference.branchEquiv p M e x C c).val.left
    (c.val.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap p M e C)
    (congrArg (fun z => z.left) (ReducedReferencePoint.CM.Reference.branchEquiv p M e x C c).property) hc
    (ReducedReferencePoint.CM.Reference.branch_left p M e x C c)
  exact hr.trans (congrArg (fun J => J.comapHom
    (PELRestrictionNaturality.CM.atPoint A U (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M e) eA x.left).abelian.hom) hb).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchKernels.CM
