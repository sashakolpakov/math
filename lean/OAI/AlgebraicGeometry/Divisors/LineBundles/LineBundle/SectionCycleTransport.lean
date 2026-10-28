import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenPullbackCoefficient

/-! # Section Cycle Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: exact transport of the actual rational-section cycle through sheaf isomorphisms and open pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}

theorem LineBundle.SectionCycleTransport.Cycles.lineBundleIso_section_pointCycle (e : L.sheaf ≅ M.sheaf) (a : X.functionFieldˣ) :
    M.rationalSectionPointCycleWithCoefficient (LineBundle.OpenDivisor.Cycles.lineBundleIsoSectionCoefficient e a) =
      L.rationalSectionPointCycleWithCoefficient a := by
  change (M.rationalSectionPointDivisorWithCoefficient _).mapRange _ _ = _
  rw [LineBundle.OpenDivisor.Cycles.lineBundleIso_section_divisor]
  rfl

variable {Y : Scheme.{0}} [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openPullback_section_pointCycle (a : X.functionFieldˣ) :
    (L.pullback i).rationalSectionPointCycleWithCoefficient (L.openPullbackSectionCoefficient i a) =
      Finsupp.comapDomain i (L.rationalSectionPointCycleWithCoefficient a) i.isOpenEmbedding.injective.injOn := by
  ext y
  exact congrArg (fun D : Y →₀ ℤ => (D y : ℚ)) (L.openPullback_section_divisor i a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
