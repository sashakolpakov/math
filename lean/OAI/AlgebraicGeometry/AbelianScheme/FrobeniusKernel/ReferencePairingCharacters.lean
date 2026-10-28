import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationPointBaseChange

/-! # Reference Pairing Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePairingCharacters

noncomputable section

/-! Every original polarization point is represented by a descended
Cartier character, and that character gives its exact CartierDuality pairing value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

attribute [local instance] DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (n : ℕ) (hn : 0 < n)
variable [IsFinite ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [Flat ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [Surjective ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n).left]

include hn in
theorem originalPolarizationCharacter_exists (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor n).obj (.op T)) :
    ∃ d : T ⟶ (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n).dual.X,
      d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n)
        (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).dual
        (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) =
      PolarizationPointBaseChange.Construction.originalNativePolarizationImage A n T y := by
  let p := HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization
  let C := DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n
  let z := IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p.map n
  obtain ⟨d, hd⟩ := IntrinsicWeilCharacterPoints.Construction.nativeCartierTorsion_surjective_points (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver
    p.representation p.map n hn C T z
  refine ⟨d, ?_⟩
  exact (congrArg (fun t => d ≫ t) (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion
    ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n) p.dual n
    (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver n) C)).symm.trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ TorsionQuotient.SubgroupFunctor.torsionι p.dual.abelian n) hd))

theorem originalPolarizationPairingValue_of_character (T : Over (Spec (.of k)))
    (x y : (A.abelian.torsionFunctor n).obj (.op T))
    (d : T ⟶ (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n).dual.X)
    (hd : d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver) ^ n)
      (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).dual
      (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) =
      PolarizationPointBaseChange.Construction.originalNativePolarizationImage A n T y) :
    DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T x y =
      (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n).evaluationValue T d
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x) := by
  let p := HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization
  exact (DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue_native A n hn T x y).trans
    (IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue_of_character (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver p.representation p.map n hn
      (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) T d
      (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x)
      (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p.map n) hd)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePairingCharacters
