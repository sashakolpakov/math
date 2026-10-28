import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice

/-! # Reference Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReferenceFrame.CM.IntrinsicReference

noncomputable section

/-! The uniform lattice denominator bound applies to the actual local
characters of the PEL model and gives GeometricTheta's standard reference frames. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice.ParameterChoices

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem standard
    (h : ∀ (τ : E →+* ℚ_[q]) (χ : NumberField.RingOfIntegers E →+* ℤ_[q]),
      (∀ a : NumberField.RingOfIntegers E, τ a = (χ a : ℚ_[q])) →
      Local.Lattice.CM.localLattice τ D.reference.lattice = Local.Lattice.CM.standard (q := q)) :
    ∀ v, CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  intro v
  exact h (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (D.localCharacter v) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReferenceFrame.CM.IntrinsicReference
