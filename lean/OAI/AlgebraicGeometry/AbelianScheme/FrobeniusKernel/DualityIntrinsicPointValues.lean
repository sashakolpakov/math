import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationPointComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingValues
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Duality Intrinsic Point Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues

noncomputable section

section

/-! The accepted CartierDuality polarization pairing agrees with the canonical
native Weil value on the original multiplication-kernel points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {S : Scheme} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A) (n : ℕ)

local instance e56PointPolarization_preserves :
    IsMonHom (show A.toOver ⟶ ell.dual.abelian from ell.map) := ell.preservesGroup

theorem e56TorsionMap_nativePoint (T : Over S) (y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n)) :
    (ell.torsionMap n).hom.app (.op T)
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y)) =
      (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk ell.dual.abelian) n).hom.hom.app (.op T)
        (ULift.up (y ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell.map n)) := by
  let f := IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver ell.dual.abelian ell.map
  have hn := congrArg (fun t => t.hom.app (.op T) (ULift.up y))
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural f n)
  exact (congrArg ((ell.torsionMap n).hom.app (.op T))
    (IntrinsicMultiplicationPointComparison.Construction.multiplicationKernelSheafIso_point (Grp.mk A.toOver) n T y)).trans hn.symm

variable [IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
    [Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
    [Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left]

def e56NativeKernelCharacterRepresentation :
    CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))) := by
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hK := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsCommMonObj K.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.toOver) ^ n)
  have : IsFinite K.X.hom := hK.1
  have : Flat K.X.hom := hK.2.1
  have : LocallyOfFinitePresentation K.X.hom := hK.2.2
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S K

theorem e56WeilPointValue_eq_native (hn : 0 < n) (T : Over S)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
    (y : T ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme ell.dual.abelian n) :
    (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((ell.weilPairing n hn).rightAdjoint.hom.app (.op T)
        ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk ell.dual.abelian) n).hom.hom.app (.op T) (ULift.up y)))
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x))).down =
      IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.toOver ell.representation ell.map n hn
        (e56NativeKernelCharacterRepresentation A n) T x y := rfl

theorem e56PolarizationPairing_nativePointValue (hn : 0 < n) (T : Over S)
    (x y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n)) :
    (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((ell.torsionPairing n hn).rightAdjoint.hom.app (.op T)
        ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y)))
      ((CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x))).down =
      IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.toOver ell.representation ell.map n hn
        (e56NativeKernelCharacterRepresentation A n) T x
        (y ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell.map n) := by
  let xs := (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x)
  let ys := (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y)
  have he := SheafPairingValues.Construction.sheafPairing_restrict_value (ell.weilPairing n hn) (𝟙 _) (ell.torsionMap n) T xs ys
  have hy := congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
    ((ell.weilPairing n hn).rightAdjoint.hom.app (.op T) z) xs) (e56TorsionMap_nativePoint A ell n T y)
  exact (congrArg ULift.down (he.trans hy)).trans
    (e56WeilPointValue_eq_native A ell n hn T x (y ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell.map n))

end Construction

end

/-! The exact canonical orthogonality predicate is triviality of the
original multiplicative-group value of the accepted CartierDuality polarization pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

attribute [local instance] e56PointPolarization_preserves

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (n : ℕ) (hn : 0 < n)

def originalPolarizationPairingValue (T : Over (Spec (.of k)))
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X :=
  (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) T
    ((CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn).rightAdjoint.hom.app (.op T)
      (Prescription.Construction.originalTorsionSheafPoint A.abelian n T y))
    (Prescription.Construction.originalTorsionSheafPoint A.abelian n T x)).down

theorem canonicalTorsionOrthogonal_iff_value (T : Over (Spec (.of k)))
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal A n hn T x y ↔ originalPolarizationPairingValue A n hn T x y = 1 :=
  ⟨congrArg ULift.down, fun h => ULift.ext _ _ h⟩

variable [IsFinite ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [Flat ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [Surjective ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]

theorem originalPolarizationPairingValue_native (T : Over (Spec (.of k)))
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    originalPolarizationPairingValue A n hn T x y =
      IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver
        (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).representation
        (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map n hn
        (e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) T
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x)
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y ≫
          CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map n) := by
  have hx := IntrinsicMultiplicationPointComparison.Construction.originalTorsionSheafPoint_kernel A.abelian n T x
  have hy := IntrinsicMultiplicationPointComparison.Construction.originalTorsionSheafPoint_kernel A.abelian n T y
  have hxy := congrArg₂ (fun a b :
      (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n).obj.obj (.op T) =>
    (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) T
      ((CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn).rightAdjoint.hom.app (.op T) b) a).down) hx hy
  exact hxy.trans (e56PolarizationPairing_nativePointValue (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian)
    (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) n hn T
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x)
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
