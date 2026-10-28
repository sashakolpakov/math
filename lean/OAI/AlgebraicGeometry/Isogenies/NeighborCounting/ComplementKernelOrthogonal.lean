import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SheafKernelAnnihilator

/-! # Complement Kernel Orthogonal -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementKernelOrthogonal

noncomputable section

/-! The actual complement square identifies kernel orthogonality.
Character-line descent detects all sections, and the target
polarization is only used on the specified torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierRestrictionDetection.Sheaf OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SheafKernelAnnihilator

variable {k : Type} [Field k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [IsCommMonObj A] [IsCommMonObj B]
variable (f : A ⟶ B) (c : B ⟶ A) [IsMonHom f] [IsMonHom c]
variable (n : ℕ) (hc : f ≫ c = (𝟙 A) ^ n)
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
variable [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
variable (hn : 0 < n)
variable [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
variable [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
variable (CM : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
variable (CF : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
variable (ellB : B ⟶ DB.withPicardGroup.abelian) [IsMonHom ellB]
variable [hmonoTarget : Mono (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementPolarizationGroupMap DB ellB)) n)]
variable (hpol : ell ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DB.withPicardGroup D.withPicardGroup c = f ≫ ellB)

def complementSourcePairing :=
  (AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn CM).restrict (𝟙 _)
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementPolarizationGroupMap D ell)) n)

include hpol CF hk in
theorem complement_kernel_character_zero_iff (T : Over (Spec (.of k)))
    (x : (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A)) n).obj.obj (.op T)) :
    ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (ComplementCharacterSquare.complementKernelTorsionEmbedding f c n hc).op).hom.app (.op T)
        ((complementSourcePairing n D ell hn CM).rightAdjoint.hom.app (.op T) x) = 1 ↔
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f)) n).hom.app (.op T) x = 1 := by
  have hmono : Mono (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f DB.withPicardGroup CF n hk) :=
    CartierRestrictionDetection.Sheaf.cartierTorsionSheaf_mono f DB.withPicardGroup CF n hk
  exact @SheafKernelAnnihilator.sheaf_square_kernel_iff _ _ _ _ _
    ((complementSourcePairing n D ell hn CM).rightAdjoint ≫
      (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (ComplementCharacterSquare.complementKernelTorsionEmbedding f c n hc).op)
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f)) n)
    (AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f DB.withPicardGroup CF n hk)
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementPolarizationGroupMap DB ellB)) n)
    hmono hmonoTarget
    ((Category.assoc _ _ _).trans
      (ComplementCharacterSquare.complement_polarization_character_square f c n hc D ell hn DB CM CF hk ellB hpol)) T x

include hpol CF hk in
theorem complement_kernel_orthogonal_iff (T : Over (Spec (.of k)))
    (x : (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A)) n).obj.obj (.op T)) :
    (∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
      (y : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op U)),
      AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A)) n) U
        ((complementSourcePairing n D ell hn CM).rightAdjoint.hom.app (.op U)
          ((AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A)) n).obj.map t.op x))
        ((ComplementCharacterSquare.complementKernelTorsionEmbedding f c n hc).hom.app (.op U) y) = 1) ↔
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f)) n).hom.app (.op T) x = 1 :=
  (SheafKernelAnnihilator.sheaf_restriction_character_zero_iff (complementSourcePairing n D ell hn CM)
    (ComplementCharacterSquare.complementKernelTorsionEmbedding f c n hc) T x).symm.trans
      (complement_kernel_character_zero_iff f c n hc D ell hn DB CM CF hk ellB hpol T x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementKernelOrthogonal
