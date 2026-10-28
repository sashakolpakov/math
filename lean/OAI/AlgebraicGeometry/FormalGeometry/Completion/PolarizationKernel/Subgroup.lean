import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Hom
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.FiniteType

/-! # Subgroup -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Subgroup

noncomputable section

/-! The actual polarization kernel is a commutative group scheme of
finite type, with a monomorphic homomorphism into the original group. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

instance polarizationKernelIsCommMonObj : IsCommMonObj (OverRepresentation.Construction.polarizationKernelOver A L) where
  mul_comm := by
    apply (cancel_mono (OverRepresentation.Construction.polarizationKernelInclusion A L)).mp
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

instance polarizationKernelOver_locallyOfFiniteType : LocallyOfFiniteType (OverRepresentation.Construction.polarizationKernelOver A L).hom := by
  change LocallyOfFiniteType ((Has.Construction.polarizationKernel A L).hom ≫ A.hom)
  infer_instance

instance polarizationKernelOver_quasiCompact : QuasiCompact (OverRepresentation.Construction.polarizationKernelOver A L).hom := by
  change QuasiCompact ((Has.Construction.polarizationKernel A L).hom ≫ A.hom)
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Subgroup
