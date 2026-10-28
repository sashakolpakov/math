import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPicardSheafRepresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.DualPicardKernel
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms

/-! # Picard Endoisogeny -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardEndoisogeny

noncomputable section

/-! Pullback by an endoisogeny is an epimorphism of the actual Picard
sheaf when the source dual is supplied. No other dual is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms.Construction.Schemes

variable {k : Type} [Field k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A A)

def picardDualEndoisogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny D.abelian D.abelian :=
  DualPicardKernel.fieldDualPicardIsogeny D D p

theorem picardDualEndoisogeny_representation :
    AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom) ≫
        (ReducedPicardSheafRepresentation.originalDualPicardSheafIso D).hom =
      (ReducedPicardSheafRepresentation.originalDualPicardSheafIso D).hom ≫ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A A p.hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  change D.representable.homEquiv (x ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D p.hom) =
    Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom A A p.hom T.unop (D.representable.homEquiv x)
  rw [Picard.Homomorphisms.DualHomomorphism.Construction.homogeneousPicardPullbackHom_apply]
  exact Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_representation D D p.hom x

include D in
theorem homogeneousPicardFppfPullback_endoisogeny_epi :
    Epi (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A A p.hom) := by
  have hp : LocallyOfFinitePresentation (picardDualEndoisogeny D p).hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [(picardDualEndoisogeny D p).hom.w]; infer_instance) inferInstance
  have he : Epi (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom)) :=
    @AbelianScheme.CartierDuality.FppfEpimorphisms.Construction.Schemes.representedFppfAbMap_epi (Spec (.of k)) (Grp.mk D.abelian.scheme) (Grp.mk D.abelian.scheme)
      inferInstance inferInstance (Grp.ofHom (picardDualEndoisogeny D p).hom)
      (picardDualEndoisogeny D p).flat (picardDualEndoisogeny D p).surjective hp
  have hc : Epi (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom) ≫
      (ReducedPicardSheafRepresentation.originalDualPicardSheafIso D).hom) := epi_comp' he inferInstance
  exact @epi_of_epi_fac (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) inferInstance _ _ _ _ _ _ hc
    (picardDualEndoisogeny_representation D p).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardEndoisogeny
