import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardSheafRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms

/-! # Picard Endoisogeny Epi -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardEndoisogenyEpi.Construction

noncomputable section

/-! Pullback by an endoisogeny is an epimorphism of the actual Picard
sheaf when the source dual is supplied. No other dual is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms.Construction.Schemes

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A A)

def picardDualEndoisogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny D.abelian D.abelian := by
  let a := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D p.hom
  have ha : IsMonHom a := by
    have hh := Picard.Homomorphisms.DualHomomorphism.Construction.dualPicardPullback_isMonHom p.hom D D
    rw [Picard.Homomorphisms.DualGroupComparison.Construction.dualPicardGroup_eq_given D] at hh
    exact hh
  have : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme a) :=
    CartierDuality.PicardKernelFiniteness.Construction.KernelCharacters.finite_geometric_dualKernel D D p.hom
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme a).hom := Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Picard.Homomorphisms.Kernel.Construction.kernelScheme a)
  have : IsFinite a.left := Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel a
  exact IsogenyQuotient.Finite.Hom.Construction.finiteAbelianHomIsogeny D.abelian D.abelian a

theorem picardDualEndoisogeny_representation :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom) ≫
        (PicardSheafRepresentation.Construction.originalDualPicardSheafIso D).hom =
      (PicardSheafRepresentation.Construction.originalDualPicardSheafIso D).hom ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A A p.hom := by
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
    Epi (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A A p.hom) := by
  have hp : LocallyOfFinitePresentation (picardDualEndoisogeny D p).hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [(picardDualEndoisogeny D p).hom.w]; infer_instance) inferInstance
  have he : Epi (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom)) :=
    @CartierDuality.FppfEpimorphisms.Construction.Schemes.representedFppfAbMap_epi (Spec (.of k)) (Grp.mk D.abelian.scheme) (Grp.mk D.abelian.scheme)
      inferInstance inferInstance (Grp.ofHom (picardDualEndoisogeny D p).hom)
      (picardDualEndoisogeny D p).flat (picardDualEndoisogeny D p).surjective hp
  have hc : Epi (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.ofHom (picardDualEndoisogeny D p).hom) ≫
      (PicardSheafRepresentation.Construction.originalDualPicardSheafIso D).hom) := epi_comp' he inferInstance
  exact @epi_of_epi_fac (CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) inferInstance _ _ _ _ _ _ hc
    (picardDualEndoisogeny_representation D p).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardEndoisogenyEpi.Construction
