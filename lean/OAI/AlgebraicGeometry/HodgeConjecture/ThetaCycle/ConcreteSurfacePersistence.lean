import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceTopologyTransport
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Persistence

/-! # Concrete Surface Persistence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSurfacePersistence.CM

noncomputable section

/-! ThetaCycle: instantiate the complete PairingContinuity proposition with actual smooth
surface forms, the actual C-infinity topology, and the computed chart
integral. The parameter family is restricted to its fixed input. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

theorem l52_actual_surface_pairing (hPairingContinuity : Persistence.CM.PairingContinuityInput.{0, 0, 0}) (S : Cm.ProjectiveSurface)
    (initial : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 2)
    (forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 2)
    (hpure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 initial.val)
    (hne : initial ≠ 0)
    (hlim : let _ := SmoothTopology.CM.smoothFormTopology S.variety.analyticModel S.variety.analyticSpace 2
      Tendsto forms atTop (𝓝 initial)) :
    ∃ n, SurfaceProjectivePairing.CM.projectiveSurfaceConjugatePairing S initial (forms n) ≠ 0 := by
  let _ := SurfaceProjectivePairing.CM.complexSurfaceChartedSpace (M := S.variety.analyticSpace) S.property
  let _ := SurfaceProjectivePairing.CM.complex_surface_real_manifold (M := S.variety.analyticSpace) S.property ∞
  let _ := SurfaceProjectivePairing.CM.complex_surface_complex_manifold (M := S.variety.analyticSpace) S.property ∞
  let _ := SmoothTopology.CM.smoothFormTopology (Fin 2 → ℂ) S.variety.analyticSpace 2
  let initial' := SurfaceProjectivePairing.CM.complexSurfaceForms S.property 2 initial
  let forms' := fun n => SurfaceProjectivePairing.CM.complexSurfaceForms S.property 2 (forms n)
  let theta : Unit → Option ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin 2 → ℂ) S.variety.analyticSpace 2 :=
    fun _ s => s.elim initial' forms'
  have hl := SurfaceTopologyTransport.CM.complex_surface_forms_tendsto S.property 2 atTop forms initial hlim
  have hself : SurfacePairing.CM.surfaceConjugatePairing initial' initial' ≠ 0 :=
    SurfaceProjectivePairing.CM.projective_surface_self_pairing_nonzero S initial hpure hne
  obtain ⟨s, hs, hp⟩ := hPairingContinuity
    (SmoothTopology.CM.smoothFormTopology (Fin 2 → ℂ) S.variety.analyticSpace 2)
    theta SurfacePairing.CM.surfaceConjugatePairing () none (fun s => ∃ n, s = some n) some
    (fun n => ⟨n, rfl⟩) hl
    (SurfacePairing.CM.surface_conjugate_pairing_continuous initial').continuousAt hself
  obtain ⟨n, rfl⟩ := hs
  exact ⟨n, hp⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSurfacePersistence.CM
