import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Transport

/-! # Realized Hodge Maps -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-! Transfer rational Hodge maps between Riemann realizations to actual
algebraic homomorphisms, conditional on the established fullness theorem. -/

open _root_.CategoryTheory

variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  {H : WeightOne.CM.WeightOneHodgeStructure U} {J : WeightOne.CM.WeightOneHodgeStructure V}

/-- The realized structure is a Hodge structure on the abelian variety's
actual rational `H¹`, transported by the given rational comparison. -/
def CMKnownResults.CM.HodgeRealization.h1HodgeStructure (R : CMKnownResults.CM.HodgeRealization H) :
    WeightOne.CM.WeightOneHodgeStructure (R.abelianVariety.variety.rationalCohomology 1) :=
  H.transport R.comparison

theorem CMKnownResults.CM.HodgeRealization.h1HodgeStructure_holomorphic (R : CMKnownResults.CM.HodgeRealization H) :
    R.h1HodgeStructure.holomorphic = R.abelianVariety.h1Holomorphic := by
  ext x
  obtain ⟨y, rfl⟩ := (R.comparison.baseChange ℚ ℂ _ _).surjective x
  exact (H.transport_holomorphic R.comparison y).trans (R.holomorphic y).symm

theorem CMKnownResults.CM.HodgeRealization.h1HodgeStructure_antiholomorphic (R : CMKnownResults.CM.HodgeRealization H) :
    R.h1HodgeStructure.antiholomorphic = R.abelianVariety.h1Antiholomorphic := by
  ext x
  obtain ⟨y, rfl⟩ := (R.comparison.baseChange ℚ ℂ _ _).surjective x
  exact (H.transport_antiholomorphic R.comparison y).trans (R.antiholomorphic y).symm

/-- Conjugate a rational map by the two actual `H¹` comparisons. -/
def CMKnownResults.CM.HodgeRealization.realizedMap (R : CMKnownResults.CM.HodgeRealization H) (S : CMKnownResults.CM.HodgeRealization J) (f : U →ₗ[ℚ] V) :
    R.abelianVariety.variety.rationalCohomology 1 →ₗ[ℚ]
      S.abelianVariety.variety.rationalCohomology 1 :=
  S.comparison.toLinearMap.comp (f.comp R.comparison.symm.toLinearMap)

theorem CMKnownResults.CM.HodgeRealization.realizedMap_isHodgeMap (R : CMKnownResults.CM.HodgeRealization H) (S : CMKnownResults.CM.HodgeRealization J)
    (f : U →ₗ[ℚ] V) (hf : WeightOne.CM.IsHodgeMap H J f) :
    WeightOne.CM.IsHodgeMap R.h1HodgeStructure S.h1HodgeStructure (R.realizedMap S f) :=
  (J.transport_isHodgeMap S.comparison).comp
    (hf.comp (H.transport_symm_isHodgeMap R.comparison))

/-- The source manuscript's rational Hodge-map transfer is an actual
rational multiple of a contravariant algebraic group pullback after
Riemann realization. -/
theorem CMKnownResults.CM.HodgeRealization.realizedMap_eq_rational_pullback
    (hknown : KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    (R : CMKnownResults.CM.HodgeRealization H) (S : CMKnownResults.CM.HodgeRealization J)
    (f : U →ₗ[ℚ] V) (hf : WeightOne.CM.IsHodgeMap H J f) :
    ∃ (r : ℚ) (g : S.abelianVariety.toOver ⟶ R.abelianVariety.toOver),
      IsMonHom g ∧ R.realizedMap S f = r • CMAbelianVariety.CM.AbelianVariety.h1Pullback g :=
  CMAbelianVariety.CM.AbelianVariety.hodgeMap_eq_rational_pullback hknown R.abelianVariety S.abelianVariety
    R.h1HodgeStructure S.h1HodgeStructure
    R.h1HodgeStructure_holomorphic R.h1HodgeStructure_antiholomorphic
    S.h1HodgeStructure_holomorphic S.h1HodgeStructure_antiholomorphic
    (R.realizedMap S f) (R.realizedMap_isHodgeMap S f hf)

end

end OAI.AlgebraicGeometry.ComplexMultiplication
