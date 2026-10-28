import OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps

/-! # Realized Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedMaps

noncomputable section

/-! Rational maps between the constructed Hodge realizations are
algebraic after a positive integer multiple. This uses the checked
native-period/HolomorphicAlgebraicity proof, with no extra fullness assumption. -/

open _root_.CategoryTheory

theorem realization_canonicalH1
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 R.abelianVariety.variety R.h1HodgeStructure :=
  ⟨R.h1HodgeStructure_holomorphic, R.h1HodgeStructure_antiholomorphic⟩

theorem exists_realized_algebraic_map
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (S : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J)
    (f : U →ₗ[ℚ] V) (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J f) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : S.abelianVariety.toOver ⟶ R.abelianVariety.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • R.realizedMap S f :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.hodge_map_algebraic_of_canonicalH1 R.abelianVariety S.abelianVariety
    R.h1HodgeStructure S.h1HodgeStructure (realization_canonicalH1 R)
    (realization_canonicalH1 S) (R.realizedMap S f) (R.realizedMap_isHodgeMap S f hf)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedMaps
