import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierDualityKernelOrthogonal
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IsogenyComplement
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison

/-! # Polarized Kernel Orthogonal -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedKernelOrthogonal

noncomputable section

/-! The actual PEL multiplier and Rosati equation imply kernel
orthogonality for the original CartierDuality source pairing. No pairing square
or annihilator identification is supplied as an extra hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IsogenyComplement OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierDualityKernelOrthogonal

variable {k : Type} [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρ)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian) (n : ℕ) (hn : 0 < n)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ n = 1)

def isogenyKernelTorsionEmbedding :=
  ComplementCharacterSquare.complementKernelTorsionEmbedding f.hom (IsogenyComplement.isogenyComplement f n hk) n
    (IsogenyComplement.isogenyComplement_projection f n hk)

include hρ in
theorem polarized_kernel_character_zero_iff
    (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ n)
    (hdegree : n.Coprime (∏ i, ε i))
    (T : Over (Spec (.of k)))
    (x : (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n).obj.obj (.op T)) :
    ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (isogenyKernelTorsionEmbedding PA PB f n hk).op).hom.app (.op T)
        ((AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing PA n hn).rightAdjoint.hom.app (.op T) x) = 1 ↔
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)) n).hom.app (.op T) x = 1 := by
  let c := IsogenyComplement.isogenyComplement f n hk
  have : IsMonHom c := IsogenyComplement.isogenyComplement_isMonHom f n hk
  have : IsMonHom (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver from f.hom) := f.preservesGroup
  have : IsMonHom (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver from c) := IsogenyComplement.isogenyComplement_isMonHom f n hk
  have : IsFinite (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver from f.hom).left := f.finite
  have : Flat (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver from f.hom).left := f.flat
  have : Surjective (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver from f.hom).left := f.surjective
  have : IsLocallyNoetherian PB.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian PB.abelian.scheme.hom
  have : IsFinite f.hom.left := f.finite
  have hlfp : LocallyOfFinitePresentation f.hom.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation (show (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian).toOver ⟶
      (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian).toOver from f.hom).left := hlfp
  have hc : f.hom ≫ c = (𝟙 PA.abelian.scheme) ^ n := IsogenyComplement.isogenyComplement_projection f n hk
  have hadj := IsogenyComplement.isogenyComplement_polarization_adjoint PA PB ρ hρ f n hk hpol
  have hd := AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled c PB.dual PA.dual
  have hcompat : (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PA.dual PA.polarization).map ≫
      Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PB.dual PB.polarization).dual
        (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PA.dual PA.polarization).dual c =
      f.hom ≫ (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PB.dual PB.polarization).map :=
    (congrArg (fun d => PA.polarization.isogeny.hom ≫ d) hd).symm.trans hadj
  have hdeg (s : Spec (.of k)) :
      n.Coprime (CartierDuality.PolarizedTorsion.Polarization.fiberDegree (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PB.dual PB.polarization) s) := by
    rw [AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourcePolarization_fiberDegree]
    exact hdegree.pow_right 2
  exact CartierDualityKernelOrthogonal.canonical_kernel_character_zero_iff (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PB.abelian)
    (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PA.dual PA.polarization) (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled PB.dual PB.polarization)
    f.hom c n hn hc hcompat hdeg T x

def canonicalKernelOrthogonal (T : Over (Spec (.of k)))
    (x : (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n).obj.obj (.op T)) : Prop :=
  ∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
    (y : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom))).obj.obj (.op U)),
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n) U
      ((AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing PA n hn).rightAdjoint.hom.app (.op U)
        ((CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n).obj.map t.op x))
      ((isogenyKernelTorsionEmbedding PA PB f n hk).hom.app (.op U) y) = 1

include hρ in
theorem polarized_kernel_orthogonal_iff
    (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ n)
    (hdegree : n.Coprime (∏ i, ε i))
    (T : Over (Spec (.of k)))
    (x : (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n).obj.obj (.op T)) :
    canonicalKernelOrthogonal PA PB f n hn hk T x ↔
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)) n).hom.app (.op T) x = 1 :=
  (SheafKernelAnnihilator.sheaf_restriction_character_zero_iff (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing PA n hn)
    (isogenyKernelTorsionEmbedding PA PB f n hk) T x).symm.trans
      (polarized_kernel_character_zero_iff PA PB ρ hρ f n hn hk hpol hdegree T x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedKernelOrthogonal
