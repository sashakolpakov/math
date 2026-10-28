import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationGradedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentChowClass

/-! # Specialization Chow Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationChowClass.BundleCycles

noncomputable section

/-! The actual Chow specialization satisfies the graph endpoint cycle-class comparison. Descent uses the independently proved vanishing of every principal relation on the smooth ambient schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphAmbientOver_separated : IsSeparated (Conormal.BundleCycles.graphAmbientOver f).hom := by
  change IsSeparated (Chow.BundleCycles.graphAmbientStructureMap f)
  infer_instance

variable [IsIntegral X.carrier] [IsIntegral Y.carrier] (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Chow.BundleCycles.graphAmbientStructureMap f))

theorem graphSpecialization_center_chowClass
    (a : DimensionChow.BundleCycles.DimensionChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (CenterEndpointFibers.BundleCycles.graphCenterSpecialEndpointOver f)
      (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphConeOver f) d p (SpecializationBettiClass.BundleCycles.graphSpecialization_codimension f d p hd)
        (Global.ChowSpecialization.BundleCycles.globalChowSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d a)) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (Conormal.BundleCycles.graphOver f)
      (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (Conormal.BundleCycles.graphAmbientOver f) d p hd a) := by
  obtain ⟨c, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (Chow.BundleCycles.graphAmbientStructureMap f) d a
  rw [Global.SpecializationComparison.BundleCycles.globalChowSpecialization_grading]
  exact SpecializationGradedClass.BundleCycles.graphSpecialization_center_cycleClass f d p hd c

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationChowClass.BundleCycles
