import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupFunctor

/-! # Group -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Group.Construction

noncomputable section

/-! The represented polarization kernel carries its actual group
scheme structure over the ground field. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

instance polarizationKernelGrpObj : GrpObj (OverRepresentation.Construction.polarizationKernelOver A L) :=
  GrpObj.ofRepresentableBy (OverRepresentation.Construction.polarizationKernelOver A L) (GroupFunctor.Construction.polarizationKernelGroupFunctor A L)
    (GroupFunctor.Construction.polarizationKernelGroupRepresentation A L)

def polarizationKernelGroupYonedaIso : yonedaGrpObj (OverRepresentation.Construction.polarizationKernelOver A L) ≅ GroupFunctor.Construction.polarizationKernelGroupFunctor A L :=
  yonedaGrpObjIsoOfRepresentableBy (OverRepresentation.Construction.polarizationKernelOver A L) (GroupFunctor.Construction.polarizationKernelGroupFunctor A L)
    (GroupFunctor.Construction.polarizationKernelGroupRepresentation A L)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Group.Construction
