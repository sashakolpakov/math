import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Subgroup
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupMonomorphismClosed

/-! # Proper -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Proper

noncomputable section

/-! The actual fppf polarization kernel is closed in the original
proper group, and is therefore proper over the ground field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

instance polarizationKernel_closed : IsClosedImmersion (Has.Construction.polarizationKernel A L).hom := by
  have : Mono (OverRepresentation.Construction.polarizationKernelInclusion A L).left :=
    inferInstanceAs (Mono (Has.Construction.polarizationKernel A L).hom)
  have : QuasiCompact (OverRepresentation.Construction.polarizationKernelInclusion A L).left :=
    inferInstanceAs (QuasiCompact (Has.Construction.polarizationKernel A L).hom)
  exact GroupMonomorphismClosed.Construction.groupMonomorphism_isClosedImmersion (OverRepresentation.Construction.polarizationKernelInclusion A L)

instance polarizationKernelOver_proper : IsProper (OverRepresentation.Construction.polarizationKernelOver A L).hom := by
  change IsProper ((Has.Construction.polarizationKernel A L).hom ≫ A.hom)
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Proper
