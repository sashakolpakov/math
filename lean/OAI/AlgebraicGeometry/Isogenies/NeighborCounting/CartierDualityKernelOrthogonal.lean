import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementKernelOrthogonal
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Duality Kernel Orthogonal -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierDualityKernelOrthogonal

noncomputable section

/-! Apply the actual character-descent argument to CartierDuality's canonical
polarization pairing. Kernel representations and torsion perfection
are constructed from the given positive polarizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare.KernelEmbedding OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementKernelOrthogonal

variable {k : Type} [Field k] (A B : CartierDuality.PolarizedTorsion.AbelianScheme (Spec (.of k)))
variable (ellA : CartierDuality.PolarizedTorsion.Polarization A) (ellB : CartierDuality.PolarizedTorsion.Polarization B)
variable (f : A.toOver ⟶ B.toOver) (c : B.toOver ⟶ A.toOver) [IsMonHom f] [IsMonHom c]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (n : ℕ) (hn : 0 < n) (hc : f ≫ c = (𝟙 A.toOver) ^ n)
variable (hpol : ellA.map ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback ellB.dual ellA.dual c = f ≫ ellB.map)
variable (hdegree : ∀ s : Spec (.of k), n.Coprime (ellB.fiberDegree s))

include hpol hdegree in
theorem canonical_kernel_character_zero_iff (T : Over (Spec (.of k))) (x : (A.torsionSheaf n).obj.obj (.op T)) :
    ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map
        (ComplementCharacterSquare.complementKernelTorsionEmbedding f c n hc).op).hom.app (.op T)
      ((ellA.torsionPairing n hn).rightAdjoint.hom.app (.op T) x) = 1 ↔
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f)) n).hom.app (.op T) x = 1 := by
  have : IsMonHom (show A.toOver ⟶ ellA.dual.abelian from ellA.map) := ellA.preservesGroup
  have : IsFinite (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.finite
  have : Flat (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.flat
  have : Surjective (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.surjective
  have : IsMonHom (show B.toOver ⟶ ellB.dual.abelian from ellB.map) := ellB.preservesGroup
  have : IsFinite (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.finite
  have : Flat (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.flat
  have : Surjective (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.surjective
  have hcover := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver ellA.dual ellA.map n hn
  have : IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hcover.1
  have : Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hcover.2.2.2
  let KM := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hKM := AbelianScheme.CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsCommMonObj KM.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.toOver) ^ n)
  have : IsFinite KM.X.hom := hKM.1
  have : Flat KM.X.hom := hKM.2.1
  have : LocallyOfFinitePresentation KM.X.hom := hKM.2.2
  let CM := CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation (Spec (.of k)) KM
  let KF := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  have hKF := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsCommMonObj KF.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f
  have : IsFinite KF.X.hom := hKF.1
  have : Flat KF.X.hom := hKF.2.1
  have : LocallyOfFinitePresentation KF.X.hom := hKF.2.2
  let CF := CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation (Spec (.of k)) KF
  have hmap : IsIso (ellB.torsionMap n) :=
    AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.torsionSheafMap_isIso B.toOver ellB.dual ellB.map n hn hdegree
  have : Mono (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
      (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementPolarizationGroupMap ellB.representation ellB.map)) n) :=
    inferInstanceAs (Mono (ellB.torsionMap n))
  exact ComplementKernelOrthogonal.complement_kernel_character_zero_iff f c n hc ellA.representation ellA.map hn ellB.representation
    CM CF (ComplementCharacterSquare.KernelEmbedding.complement_kernel_point_bound f c n hc) ellB.map hpol T x

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierDualityKernelOrthogonal
