import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Padic Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PadicExt.TestTransport

noncomputable section

/-! All actual rational p-adic projections distinguish finite adeles. -/

open scoped Classical

open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

theorem finitePadicProjection_ext (a b : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (h : ∀ p : ℕ, ∀ [Fact p.Prime], RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p a = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p b) : a = b := by
  apply DFunLike.ext
  intro v
  let p := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) v).val
  let : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv (R := ℤ) v).property⟩
  have hv : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p = v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm_apply_apply v
  have he := congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p) (h p)
  change (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p) ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p) a)) =
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p) ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p) b)) at he
  rw [ContinuousAlgEquiv.apply_symm_apply, ContinuousAlgEquiv.apply_symm_apply, hv] at he
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PadicExt.TestTransport
