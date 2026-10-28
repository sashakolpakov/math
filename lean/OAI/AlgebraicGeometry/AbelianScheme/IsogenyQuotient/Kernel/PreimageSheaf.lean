import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageExactness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability

/-! # Preimage Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageSheaf.Construction

noncomputable section

/-! The actual restricted quotient represents its fppf cokernel.
The target is the genuine complementary kernel, with its finite locally
free geometry supplied by the proved kernel isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Schemes
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (r : B ⟶ C) [IsMonHom r]

def kernelPreimageGroupInclusion : Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) ⟶ Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r)) :=
  Grp.homMk (PreimageExactness.Construction.kernelPreimageInclusion f r)

variable [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom] [Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]
  [LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject r).hom]

def kernelPreimageNativeQuotient : CartierDuality.IntrinsicQuotients.Construction.Schemes.NativeFiniteLocallyFreeQuotient (kernelPreimageGroupInclusion f r) := by
  let hp := Picard.PoincareBundle.Kernel.PreimageQuotient.finite_flat_surjective f r
  have hpfp : LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.PreimageQuotient.map f r).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (Picard.PoincareBundle.Kernel.PreimageQuotient.underlying_isPullback f r) inferInstance
  exact {
    quotient := Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r)
    commutative := inferInstance
    finite := inferInstance
    flat := inferInstance
    finitelyPresented := inferInstance
    projection := Grp.homMk (Picard.PoincareBundle.Kernel.PreimageQuotient.map f r)
    projectionFinite := hp.1
    projectionFlat := hp.2.1
    projectionFinitelyPresented := hpfp
    projectionSurjective := hp.2.2
    kernel := PreimageExactness.Construction.kernelPreimage_kernel_iff f r
  }

set_option backward.isDefEq.respectTransparency false in
def kernelPreimageSheafQuotientIso :
    cokernel (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelPreimageGroupInclusion f r)) ≅
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r)) := by
  have : Mono (kernelPreimageGroupInclusion f r).hom.hom :=
    inferInstanceAs (Mono (PreimageExactness.Construction.kernelPreimageInclusion f r))
  have : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelPreimageGroupInclusion f r)) :=
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (kernelPreimageGroupInclusion f r)
  exact (kernelPreimageNativeQuotient f r).sheafCokernelIso

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageSheaf.Construction
