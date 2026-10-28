import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Group

/-! # Hom -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Hom

noncomputable section

/-! The universal inclusion of the actual polarization kernel is
a homomorphism of the derived group schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

def polarizationKernelGroupInclusion : Grp.mk (OverRepresentation.Construction.polarizationKernelOver A L) ⟶ Grp.mk A :=
  yonedaGrpFullyFaithful.preimage
    ((Group.Construction.polarizationKernelGroupYonedaIso A L).hom ≫ GroupFunctor.Construction.polarizationKernelGroupFunctorInclusion A L)

theorem polarizationKernelGroupInclusion_hom :
    (polarizationKernelGroupInclusion A L).hom.hom = OverRepresentation.Construction.polarizationKernelInclusion A L := by
  have h := yonedaGrpFullyFaithful.map_preimage
    (X := Grp.mk (OverRepresentation.Construction.polarizationKernelOver A L)) (Y := Grp.mk A)
    ((Group.Construction.polarizationKernelGroupYonedaIso A L).hom ≫ GroupFunctor.Construction.polarizationKernelGroupFunctorInclusion A L)
  have hv := ConcreteCategory.congr_hom (congr_app h (op (OverRepresentation.Construction.polarizationKernelOver A L))) (𝟙 (OverRepresentation.Construction.polarizationKernelOver A L))
  change (𝟙 (OverRepresentation.Construction.polarizationKernelOver A L)) ≫ (polarizationKernelGroupInclusion A L).hom.hom =
    (𝟙 (OverRepresentation.Construction.polarizationKernelOver A L)) ≫ (OverRepresentation.Construction.polarizationKernelInclusion A L ≫ 𝟙 A) at hv
  simpa only [Category.id_comp, Category.comp_id] using hv

instance polarizationKernelInclusion_isMonHom : IsMonHom (OverRepresentation.Construction.polarizationKernelInclusion A L) := by
  rw [← polarizationKernelGroupInclusion_hom A L]
  exact (polarizationKernelGroupInclusion A L).hom.isMonHom_hom

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Hom
