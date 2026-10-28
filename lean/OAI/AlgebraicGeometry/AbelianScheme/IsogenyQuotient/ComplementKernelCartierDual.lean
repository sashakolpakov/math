import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianCokernelDual
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedGroupIsoReflection
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Complement Kernel Cartier Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementKernelCartierDual.Construction

noncomputable section

/-! Full self-annihilation identifies the actual complementary kernel
with the Cartier dual of the original quotient kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (r : B ⟶ C) [IsMonHom r]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom] [Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]
  [LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]

local instance complementKernelSubgroup_mono :
    Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)) := by
  have : Mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r).hom.hom :=
    inferInstanceAs (Mono (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r))
  exact CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)

variable (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r))))
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r)))))
  (he : e.IsPerfect)
  (hlag : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e (Subobject.mk (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r))) =
    Subobject.mk (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)))

def complementKernelCartierSheafIso :
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r)) ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f))) := by
  have : Mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r).hom.hom :=
    inferInstanceAs (Mono (Kernel.PreimageExactness.Construction.kernelPreimageInclusion f r))
  have : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)) :=
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)
  have hb : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (cokernel (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)))) :=
    (CartierDuality.PolarizedTorsion.Construction.cartier_duality _ (Kernel.PreimageSheaf.Construction.kernelPreimageNativeQuotient f r).sheafCokernel_finiteLocallyFree).2.2.1
  exact (Kernel.PreimageSheaf.Construction.kernelPreimageSheafQuotientIso f r).symm ≪≫
    LagrangianCokernelDual.Construction.lagrangianCokernelDualIso (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Kernel.PreimageSheaf.Construction.kernelPreimageGroupInclusion f r)) e he hlag

def complementKernelCartierGroupIso
    (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f))) :
    Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) ≅ Y.dual := by
  let : IsCommMonObj Y.dual.X := Y.commutative
  exact RepresentedGroupIsoReflection.Construction.groupIsoOfRepresentedFppfAbIso _ _
    (complementKernelCartierSheafIso f r e he hlag ≪≫ Y.representedCartierDualIso.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplementKernelCartierDual.Construction
