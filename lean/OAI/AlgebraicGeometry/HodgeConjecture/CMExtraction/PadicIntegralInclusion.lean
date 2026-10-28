import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Theta.IntegralAdeles
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseIntegralSubrings

/-! # Padic Integral Inclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralInclusion.TestTransport

noncomputable section

/-! The prescribed local completion map sends each p-adic integer
into the actual integral completion, by integer density. -/

open IsDedekindDomain

open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

theorem rationalCompletionIntegers_closed (v : HeightOneSpectrum ℤ) :
    IsClosed (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  (isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))).isClosed

theorem padicCoordinate_integer_mem (q : ℕ) [Fact q.Prime] (x : PadicInt q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q (x : Padic q) ∈ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q).adicCompletionIntegers ℚ :=
  DenseIntegralSubrings.TestTransport.ringHom_mem_of_dense_integers (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q).continuous
    (PadicInt.subring q) ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q).adicCompletionIntegers ℚ).toSubring
    PadicInt.denseRange_intCast (rationalCompletionIntegers_closed (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q)) x.property

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralInclusion.TestTransport
