import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticePrimeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticePadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayLatticeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalizedLatticeMaps
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinateSplit

/-! # Lattice Split -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticeSplit.ParameterChoices

noncomputable section

/-! Split membership in the original completed lattice into membership
in its rational localization and its full native q-adic image. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ D.reference.lattice] (b : Module.Basis J ℤ D.reference.lattice)

include hg hq in
theorem native_completed_lattice_split
    (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) (x : Fin 3 → E)
    (haway : ∀ j (p : ℕ) [Fact p.Prime], p ≠ q →
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
        (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y j) =
          algebraMap ℚ (Padic p) ((b.extendOfIsLattice ℚ).equivFun x j)) :
    Y ∈ D.reference.completedLattice ↔
      x ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ∧
        (fun v i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (Y i)) ∈
          SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice :=
  (LatticePrimeCoordinates.ParameterChoices.native_completed_lattice_prime_coordinates E D b Y).trans
    ((AdelicCoordinateSplit.TestTransport.adelic_coordinate_norm_split q
      (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y)
      ((b.extendOfIsLattice ℚ).equivFun x) haway).trans
        (and_congr (LatticePrimeCoordinates.ParameterChoices.native_away_lattice_prime_coordinates E D b x).symm
          (LatticePrimeCoordinates.ParameterChoices.native_split_completed_prime_coordinates E D b hg hq Y).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticeSplit.ParameterChoices
