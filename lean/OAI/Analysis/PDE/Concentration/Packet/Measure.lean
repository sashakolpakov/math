import OAI.Analysis.PDE.Concentration.Packet.Coordinates
import OAI.Analysis.PDE.Concentration.Physical.LatticeChart
import OAI.Analysis.PDE.Concentration.Input.Integrability

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem measurePreserving_spatialPiCoordinates (d : ℕ) :
    MeasurePreserving (spatialPiCoordinates d) := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) => ℝ) (finSuccEquiv d).symm).comp
    (PiLp.volume_preserving_ofLp (Option (Fin d)))
  convert h using 1
  ext y i
  simp [spatialPiCoordinates_apply, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

/-- The physical coordinate split with the same Euclidean spatial volume as
the packet Fourier estimates. -/
def physicalPacketSplit (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 ≃ᵐ
    (OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ)) :=
  (OAI.Analysis.PDE.Green.physicalSpatialEquiv d).trans
    (((spatialPiCoordinates d).symm.toHomeomorph.toMeasurableEquiv).prodCongr
      (MeasurableEquiv.refl _))

theorem physicalPacketSplit_symm (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    (physicalPacketSplit d).symm (y, q) = spatialPacketEmbedding d y q := by
  change OAI.Analysis.PDE.Green.physicalSpatialEmbedding d (spatialPiCoordinates d y) q = _
  unfold spatialPacketEmbedding
  congr 1
  ext i
  exact spatialPiCoordinates_apply y i

theorem physicalPacketSplit_apply (d : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalPacketSplit d y = (physicalSpatialRealVector d y, OAI.Analysis.PDE.Green.physicalSpatialProjection d y) := by
  apply (physicalPacketSplit d).symm.injective
  rw [MeasurableEquiv.symm_apply_apply, physicalPacketSplit_symm]
  apply (OAI.Analysis.PDE.Green.physicalSpatialEquiv d).injective
  change OAI.Analysis.PDE.Green.physicalSpatialEquiv d y =
    OAI.Analysis.PDE.Green.physicalSpatialEquiv d ((OAI.Analysis.PDE.Green.physicalSpatialEquiv d).symm _)
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    simp [OAI.Analysis.PDE.Green.physicalSpatialEquiv_fst, physicalSpatialRealVector]
  · exact (OAI.Analysis.PDE.Green.physicalSpatialProjection_eq d y).symm

theorem measurePreserving_physicalPacketSplit (d : ℕ) :
    MeasurePreserving (physicalPacketSplit d) := by
  have hi := MeasurePreserving.symm (spatialPiCoordinates d).toHomeomorph.toMeasurableEquiv
    (measurePreserving_spatialPiCoordinates d)
  apply (OAI.Analysis.PDE.Green.measurePreserving_physicalSpatialEquiv d).trans
  simp only [Measure.volume_eq_prod]
  convert hi.prod (MeasurePreserving.id (volume : Measure (Option (Fin d) → ℂ))) using 1
  ext p
  all_goals rfl

theorem physicalPacketSplit_setIntegral {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    {T : Set (Option (Fin d) → ℂ)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hf : IntegrableOn f ((physicalPacketSplit d) ⁻¹' (S ×ˢ T))) :
    (∫ y in (physicalPacketSplit d) ⁻¹' (S ×ˢ T), f y) =
      ∫ q in T, ∫ x in S, f (spatialPacketEmbedding d x q) := by
  let e := physicalPacketSplit d
  have hST : MeasurableSet (S ×ˢ T) := hS.prod hT
  have hpre : MeasurableSet (e ⁻¹' (S ×ˢ T)) := hST.preimage e.measurable
  have hmp := (measurePreserving_physicalPacketSplit d).symm
  have hi := hmp.integrable_comp_of_integrable ((integrable_indicator_iff hpre).mpr hf)
  have heq : (fun p => ((e ⁻¹' (S ×ˢ T)).indicator f) (e.symm p)) =
      (S ×ˢ T).indicator (fun p => f (spatialPacketEmbedding d p.1 p.2)) := by
    ext p
    have hp : e.symm p ∈ e ⁻¹' (S ×ˢ T) ↔ p ∈ S ×ˢ T := by
      change e (e.symm p) ∈ S ×ˢ T ↔ _
      rw [e.apply_symm_apply]
    by_cases h : p ∈ S ×ˢ T
    · rw [Set.indicator_of_mem (hp.mpr h), Set.indicator_of_mem h]
      congr 1
      exact physicalPacketSplit_symm d p.1 p.2
    · rw [Set.indicator_of_notMem (fun hc => h (hp.mp hc)), Set.indicator_of_notMem h]
  change Integrable (fun p => ((e ⁻¹' (S ×ˢ T)).indicator f) (e.symm p)) volume at hi
  rw [heq] at hi
  have hip := (integrable_indicator_iff hST).mp hi
  rw [← integral_indicator hpre, ← hmp.integral_comp e.symm.measurableEmbedding, heq,
    integral_indicator hST]
  rw [Measure.volume_eq_prod] at hip ⊢
  rw [setIntegral_prod _ hip]
  exact integral_integral_swap (by simpa only [Measure.prod_restrict, IntegrableOn, Function.uncurry_def] using hip)

end OAI.Analysis.PDE.Concentration
