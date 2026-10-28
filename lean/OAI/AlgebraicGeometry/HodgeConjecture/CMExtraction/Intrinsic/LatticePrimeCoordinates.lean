import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticePadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayLatticeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalizedLatticeMaps
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.Lattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.IntegralCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinatePredicate

/-! # Lattice Prime Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticePrimeCoordinates.ParameterChoices

noncomputable section

/-! Prime-coordinate criteria for the three original native lattices. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ D.reference.lattice] (b : Module.Basis J ℤ D.reference.lattice)

omit [IsGalois ℚ E] in
theorem native_completed_lattice_prime_coordinates (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    Y ∈ D.reference.completedLattice ↔ ∀ j (p : ℕ) [Fact p.Prime],
      ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y j)‖ ≤ 1 :=
  IntegralCoordinatePredicate.TestTransport.integral_coordinate_predicate (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y)
    (PEL.IntegralCoordinates.TestTransport.pel_completed_integral_coordinates E D.reference b Y)

omit [IsGalois ℚ E] [DecidableEq J] in
theorem native_away_lattice_prime_coordinates (x : Fin 3 → E) :
    x ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ↔ ∀ j (p : ℕ) [Fact p.Prime], p ≠ q →
      ‖((b.extendOfIsLattice ℚ).equivFun x j : Padic p)‖ ≤ 1 :=
  AwayLatticeCoordinates.TestTransport.awayLattice_padic_coordinates D.reference.lattice b q x

theorem native_split_completed_prime_coordinates (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (fun v i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (Y i)) ∈
      SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice ↔
        ∀ j, ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun Y j)‖ ≤ 1 := by
  constructor
  · intro h j
    have hj := (SplitCoordinates.ParameterChoices.nativeSplitLattice_coordinates E D hg hq b _).mp h j
    have he := congr_fun (SplitCoordinates.ParameterChoices.nativeSplitCoordinates_completed E D hg hq (b.extendOfIsLattice ℚ).equivFun Y) j
    exact he ▸ hj
  · intro h
    apply (SplitCoordinates.ParameterChoices.nativeSplitLattice_coordinates E D hg hq b _).mpr
    intro j
    have he := congr_fun (SplitCoordinates.ParameterChoices.nativeSplitCoordinates_completed E D hg hq (b.extendOfIsLattice ℚ).equivFun Y) j
    exact he.symm ▸ h j

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticePrimeCoordinates.ParameterChoices
