import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePairingCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceCartierRepresentation

/-! # Reference Pullback Pairing Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePullbackPairingCharacters

noncomputable section

/-! Original pairing values on the pulled-back source use its actual
Cartier character point, with the original bundled Picard data retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {k k' : Type} [Field k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (s : Spec (.of k') ⟶ Spec (.of k)) (n : ℕ) (hn : 0 < n)

local instance originalPullbackScheme_comm : IsCommMonObj ((Over.pullback s).obj A.abelian.scheme) :=
  (A.abelian.pullback s).commutative

variable [IsFinite ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian).toOver) ^ n).left]
    [Flat ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian).toOver) ^ n).left]
    [Surjective ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian).toOver) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian).toOver) ^ n).left]
variable [IsFinite ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left]
    [Flat ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left]
    [Surjective ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left]

theorem originalPullbackPairingValue_of_character (Q : Over (Spec (.of k')))
    (x y : ((A.pullback s).abelian.torsionFunctor n).obj (.op Q))
    (d : Q ⟶ (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation
      (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian) n).dual.X)
    (hd : d ≫ ReferenceCartierRepresentation.Construction.originalCartierPullbackMap A.dual s
      ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n)
      (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian) n) =
      PolarizationPointBaseChange.Construction.originalNativePolarizationImage (A.pullback s) n Q y) :
    DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue (A.pullback s) n hn Q x y =
      (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian) n).evaluationValue
        Q d (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint (A.pullback s).abelian n Q x) := by
  apply ReferencePairingCharacters.Construction.originalPolarizationPairingValue_of_character (A.pullback s) n hn Q x y d
  refine Eq.trans ?_ hd
  apply congrArg (fun z :
    (DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian) n).dual.X ⟶
      (Over.pullback s).obj A.dual.abelian.scheme => d ≫ z)
  rfl

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePullbackPairingCharacters
