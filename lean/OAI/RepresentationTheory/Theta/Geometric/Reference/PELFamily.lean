import OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationConstruction
import OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualAction

/-! # PEL Family -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! The constructed polarized reference fiber carries the original CM
action, fixed marking, geometric signature, and dual-action intertwining. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualAction

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PolarizationConstruction.ReferencePolarizationConstruction p)

def PolarizationConstruction.ReferencePolarizationConstruction.pelFamily (level : ℕ) [NeZero level] :
    AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized (C.polarized level) M.functorAction

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_signature (level : ℕ) [NeZero level] :
    (C.pelFamily level).HasPrescribedLieSignature P (LieSignature.referenceComplexBaseAction P) := by
  intro k _ _ t τ
  exact LieSignature.reference_geometric_lie_signature M k t τ

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_kernelType (level : ℕ) [NeZero level] :
    (C.pelFamily level).polarizationMap.HasPolarizationType P.polarizationType :=
  p.hasPolarizationType

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_positive (level : ℕ) [NeZero level]
    (k : Type) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (C.pelFamily level).dual (C.pelFamily level).polarizationMap.hom k t :=
  C.polarization.positive k t

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_dualAction_intertwining (level : ℕ) [NeZero level]
    (a : NumberField.RingOfIntegers E) :
    (C.pelFamily level).polarizationMap.hom ≫
        AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap N.abelianScheme.scheme
          (N.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a)) =
      AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap (C.pelFamily level).abelian.scheme
        ((C.pelFamily level).action (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ≫
          (C.pelFamily level).polarizationMap.hom :=
  (p.integralAction_intertwining (NumberField.IsCMField.ringOfIntegersComplexConj E a)).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
