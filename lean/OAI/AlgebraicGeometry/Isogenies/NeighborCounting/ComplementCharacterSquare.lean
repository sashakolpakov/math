import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierTorsionSource
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor

/-! # Complement Character Square -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare

noncomputable section

section

/-! A complementary isogeny gives the actual character-restriction
square for its kernel inside multiplication torsion. The square uses
the normalized character-line construction of CartierDuality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierTorsionSource

variable {S : Scheme} {A B : Over S} [GrpObj A] [GrpObj B]
variable [IsCommMonObj A] [IsCommMonObj B]
variable (f : A ⟶ B) (c : B ⟶ A) [IsMonHom f] [IsMonHom c]
variable (n : ℕ) (hc : f ≫ c = (𝟙 A) ^ n)

include hc in
omit [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] [IsMonHom f] [IsMonHom c] in
theorem complement_kernel_square : (𝟙 A) ≫ (𝟙 A) ^ n = f ≫ c :=
  (Category.id_comp _).trans hc.symm

def complementKernelTorsionEmbedding :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ⟶
      AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n :=
  AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
      (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap ((𝟙 A) ^ n) f (𝟙 A) c (complement_kernel_square f c n hc)) ≫
    (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom

variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
variable [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
variable (hn : 0 < n)
variable [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
variable [Surjective ((𝟙 A : A ⟶ A) ^ n).left]
variable [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
variable (CM : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
variable (CF : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

omit [IsCommMonObj B] in
theorem complement_character_descent_square :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
    letI : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (complementKernelTorsionEmbedding f c n hc).op ≫
        AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f DB CF n hk =
      (AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn CM).hom ≫
        AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierTorsionSource.nativePicardSourceMap c D.withPicardGroup DB)) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
  have : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
  have hs := CartierTorsionSource.cartierTorsionSheaf_source ((𝟙 A) ^ n) f (𝟙 A) c
    (complement_kernel_square f c n hc) D.withPicardGroup DB CM CF n
    (AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) hk
  change (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map
      (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap ((𝟙 A) ^ n) f (𝟙 A) c (complement_kernel_square f c n hc)) ≫
          (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom).op ≫ _ = _
  erw [op_comp, Functor.map_comp, Category.assoc, hs]
  exact (Category.assoc _ _ _).symm

omit [IsCommMonObj B] in
theorem complement_weil_character_square :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
    letI : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
    (AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn CM).rightAdjoint ≫
        (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (complementKernelTorsionEmbedding f c n hc).op ≫
        AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f DB CF n hk =
      AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierTorsionSource.nativePicardSourceMap c D.withPicardGroup DB)) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup DB
  have : IsCommMonObj DB.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative DB
  erw [complement_character_descent_square f c n hc D ell hn DB CM CF hk, AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing_rightAdjoint]
  exact (AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A D ell n hn CM).inv_hom_id_assoc _

def complementSourceGroupMap : Grp.mk A ⟶ Grp.mk B := Grp.homMk f

def complementPolarizationGroupMap : Grp.mk A ⟶ Grp.mk D.withPicardGroup.abelian := Grp.homMk ell

theorem complement_polarization_character_square
    (ellB : B ⟶ DB.withPicardGroup.abelian) [IsMonHom ellB]
    (hpol : ell ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DB.withPicardGroup D.withPicardGroup c = f ≫ ellB) :
    ((AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A D ell n hn CM).restrict (𝟙 _)
        (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (complementPolarizationGroupMap D ell)) n)).rightAdjoint ≫
        (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (complementKernelTorsionEmbedding f c n hc).op ≫
        AbelianScheme.CartierDuality.PicardSheaf.Construction.KernelCharacters.cartierToPicardTorsionSheaf f DB.withPicardGroup CF n hk =
      AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (complementSourceGroupMap f)) n ≫
        AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (complementPolarizationGroupMap DB ellB)) n := by
  let p := complementPolarizationGroupMap D ell
  let d := CartierTorsionSource.nativePicardSourceMap c D.withPicardGroup DB.withPicardGroup
  let r := complementSourceGroupMap f
  let pB : Grp.mk B ⟶ Grp.mk DB.withPicardGroup.abelian := Grp.homMk ellB
  have hg : p ≫ d = r ≫ pB := by
    apply Grp.hom_ext
    exact hpol
  have hr : AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d =
      AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫ AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap pB :=
    (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp p d).symm.trans
      ((congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap w) hg).trans (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp r pB))
  erw [AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_rightAdjoint, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.assoc]
  erw [complement_weil_character_square f c n hc D ell hn DB.withPicardGroup CM CF hk]
  exact AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction.torsionSheafMap_square _ _ _ _ hr n

end

/-! The complement-defined torsion embedding has the original kernel
inclusion. Its sections are exactly the original kernel sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace KernelEmbedding

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare

variable {S : Scheme} {A B : Over S} [GrpObj A] [GrpObj B]
variable [IsCommMonObj A] [IsCommMonObj B]
variable (f : A ⟶ B) (c : B ⟶ A) [IsMonHom f] [IsMonHom c]
variable (n : ℕ) (hc : f ≫ c = (𝟙 A) ^ n)

def originalKernelGroupInclusion : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) ⟶ Grp.mk A :=
  Grp.homMk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)

include hc in
omit [IsCommMonObj B] in
theorem complement_kernel_point_bound (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) : x ^ n = 1 := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  calc
    (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ^ n = (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ (𝟙 A) ^ n := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ f ≫ c := congrArg (fun w => (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ w) hc.symm
    _ = 1 := by
      rw [Category.assoc, ← Category.assoc (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) f c, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp,
        MonObj.one_comp, MonObj.comp_one]

theorem multiplicationKernelSheafIso_original_inclusion :
    (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom ≫
        kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) =
      AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (originalKernelGroupInclusion ((𝟙 A) ^ n)) := by
  let e := (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom
  have hg : e ≫ AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion (Grp.mk A) n = originalKernelGroupInclusion ((𝟙 A) ^ n) := by
    apply Grp.hom_ext
    exact Category.id_comp _
  change (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap e ≫ (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A) n).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap e ≫ w) (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion (Grp.mk A) n)).trans
      ((AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp e (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion (Grp.mk A) n)).symm.trans
        (congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap w) hg)))

omit [IsCommMonObj B] in
theorem complementKernelTorsionEmbedding_inclusion :
    complementKernelTorsionEmbedding f c n hc ≫
        kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) =
      AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (originalKernelGroupInclusion f) := by
  let r := AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap ((𝟙 A) ^ n) f (𝟙 A) c (complement_kernel_square f c n hc)
  have hg : r ≫ originalKernelGroupInclusion ((𝟙 A) ^ n) = originalKernelGroupInclusion f := by
    apply Grp.hom_ext
    exact (AbelianScheme.FrobeniusKernel.CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion ((𝟙 A) ^ n) f (𝟙 A) c
      (complement_kernel_square f c n hc)).trans (Category.comp_id _)
  change (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫ (AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r ≫ w) (multiplicationKernelSheafIso_original_inclusion n)).trans
      ((AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp r (originalKernelGroupInclusion ((𝟙 A) ^ n))).symm.trans
        (congrArg (fun w => AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap w) hg)))

theorem complementKernelTorsionEmbedding_mono : Mono (complementKernelTorsionEmbedding f c n hc) := by
  have : Mono (originalKernelGroupInclusion f).hom.hom :=
    inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  have : Mono (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (originalKernelGroupInclusion f)) :=
    AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (originalKernelGroupInclusion f)
  exact mono_of_mono_fac (complementKernelTorsionEmbedding_inclusion f c n hc)

end KernelEmbedding

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare
