import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding

/-! # Split Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLattice.ParameterChoices

noncomputable section

/-! The native good-prime completion map gives the product decomposition
of the original reference lattice under its original local characters. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct.TestTransport

variable (E : Type) [Field E] [NumberField E] [IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_split_lattice_product (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) :
    SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice =
      Submodule.pi Set.univ (SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) := by
  have hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice D.reference.lattice := by
    rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  exact SplitLatticeProduct.TestTransport.splitLatticeImage_eq_product (algebraMap (𝓞 E) E) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.localCharacter
    (fun v a => (LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D v a).symm)
    D.reference.lattice hL.2.2 hq.1.surjective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLattice.ParameterChoices
