import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationBettiClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ClassDegreePullback

/-! # Specialization Graded Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationGradedClass.BundleCycles

noncomputable section

/-! The full specialization comparison in the degree convention of the requested cycle-class naturality theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f))

theorem graphSpecialization_center_cycleClass
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Chow.BundleCycles.graphAmbientStructureMap f) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass (Conormal.BundleCycles.graphConeOver f) d p (SpecializationBettiClass.BundleCycles.graphSpecialization_codimension f d p hd)
        (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d c)) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (Conormal.BundleCycles.graphOver f)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd c) := by
  exact (Graded.ClassDegreePullback.BundleCycles.schemeGradedCycleClass_betti_degreeTransport (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f) d p
    (SpecializationBettiClass.BundleCycles.graphSpecialization_codimension f d p hd) _).trans
      ((congrArg (Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv X.toOver (two_mul p))
        (SpecializationBettiClass.BundleCycles.graphSpecialization_center_absoluteClass f d p hd c)).trans
          (Graded.ClassDegreePullback.BundleCycles.schemeGradedCycleClass_betti_degreeTransport (Conormal.BundleCycles.graphOver f) d p hd c).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationGradedClass.BundleCycles
