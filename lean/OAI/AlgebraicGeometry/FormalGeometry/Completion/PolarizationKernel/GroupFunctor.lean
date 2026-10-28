import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupCondition
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.OverRepresentation

/-! # Group Functor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupFunctor

noncomputable section

/-! The represented polarization kernel is naturally a presheaf of
actual groups, with its inclusion into the group's point functor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

def polarizationKernelRestriction {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) :
    GroupCondition.Construction.polarizationKernelPoints A L T →* GroupCondition.Construction.polarizationKernelPoints A L U where
  toFun x := ⟨j ≫ x.val, (PolarizationKernel.Functor.Construction.polarizationKernelSubfunctor A L).map j.op x.property⟩
  map_one' := Subtype.ext (MonObj.comp_one j)
  map_mul' x y := Subtype.ext (MonObj.comp_mul j x.val y.val)

def polarizationKernelGroupFunctor : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (GroupCondition.Construction.polarizationKernelPoints A L T.unop)
  map f := GrpCat.ofHom (polarizationKernelRestriction A L f.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.id_comp x.val)
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ _)

def polarizationKernelGroupFunctorForgetIso :
    polarizationKernelGroupFunctor A L ⋙ forget GrpCat ≅ (PolarizationKernel.Functor.Construction.polarizationKernelSubfunctor A L).toFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def polarizationKernelGroupRepresentation :
    (polarizationKernelGroupFunctor A L ⋙ forget GrpCat).RepresentableBy (OverRepresentation.Construction.polarizationKernelOver A L) :=
  Functor.representableByEquiv.symm
    (OverRepresentation.Construction.polarizationKernelPointIso A L ≪≫ (polarizationKernelGroupFunctorForgetIso A L).symm)

def polarizationKernelGroupFunctorInclusion : polarizationKernelGroupFunctor A L ⟶ yonedaGrpObj A where
  app T := GrpCat.ofHom (GroupCondition.Construction.polarizationKernelPoints A L T.unop).subtype
  naturality {_ _} _ := rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupFunctor
