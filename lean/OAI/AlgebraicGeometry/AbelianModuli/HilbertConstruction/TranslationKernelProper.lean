import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericLiftingClosedMono
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericZeroLift
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme

/-! # Translation Kernel Proper -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelProper

noncomputable section

/-! The original Picard zero locus is closed. In particular, the actual
translation kernel of a line bundle on an abelian scheme is proper. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Theta.Geometric.RelativeRigidifiedCharts
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelProper

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

theorem zeroScheme_localGenericLifting : Local.GenericLifting.LocalGenericLifting (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom := by
  intro T _ _ _ _ _ a z h
  let V : Over S := Over.mk (a ≫ B.hom)
  let : IsAffine V.left := inferInstanceAs (IsAffine T)
  let : IsLocallyNoetherian V.left := inferInstanceAs (IsLocallyNoetherian T)
  let : IsIntegral V.left := inferInstanceAs (IsIntegral T)
  let : IsLocalRing Γ(V.left, ⊤) := inferInstanceAs (IsLocalRing Γ(T, ⊤))
  let : IsNoetherianRing Γ(V.left, ⊤) := inferInstanceAs (IsNoetherianRing Γ(T, ⊤))
  let a' : V ⟶ B := Over.homMk a rfl
  obtain ⟨w, hw⟩ := Picard.ThetaConstruction.GenericZeroLift.Geometric.RelativeRigidifiedCharts.zeroScheme_generic_lift P D a' z h
  exact ⟨w.left, congrArg Over.Hom.left hw⟩

theorem zeroScheme_closedImmersion : IsClosedImmersion (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom :=
  (zeroScheme_localGenericLifting P D).closedImmersion _

theorem zeroInclusion_closedImmersion : IsClosedImmersion (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P).left :=
  zeroScheme_closedImmersion P D

end Theta.Geometric.RelativeRigidifiedCharts

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

theorem translationKernel_inclusion_closedImmersion :
    IsClosedImmersion (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).left :=
  Theta.Geometric.RelativeRigidifiedCharts.zeroInclusion_closedImmersion P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)

theorem translationKernel_proper : IsProper (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let : IsClosedImmersion (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).left :=
    translationKernel_inclusion_closedImmersion A L P
  have h : IsProper ((Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).left ≫ A.scheme.hom) := inferInstance
  exact (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).w ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationKernelProper
