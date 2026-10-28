import OAI.Analysis.PDE.Concentration.FullSplit
import OAI.Analysis.PDE.Green.Physical.JointExtension

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- Joint smoothness on a neighborhood of the closed spatial fibers at
admissible times. No regularity is required at the degenerate inner time
boundary, the outer time boundary, or away from the closed fibers. -/
def PacketLocalSmooth (d : ℕ) (a : ℝ) (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) : Prop :=
  ∃ U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3), IsOpen U ∧ ContDiffOn ℝ ∞ u U ∧
    ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0 → x ∈ U

theorem PacketLocalSmooth.contDiffAt {d : ℕ} {a : ℝ}
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : PacketLocalSmooth d a u)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3}
    (ht : a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) : ContDiffAt ℝ ∞ u x := by
  obtain ⟨U, hU, hu, hcontains⟩ := hu
  exact (hu x (hcontains x ht hr)).contDiffAt (hU.mem_nhds (hcontains x ht hr))

theorem packetLocalSmooth_of_contDiff {d : ℕ} {a : ℝ}
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : ContDiff ℝ ∞ u) : PacketLocalSmooth d a u :=
  ⟨univ, isOpen_univ, hu.contDiffOn, fun _ _ _ => mem_univ _⟩

def packetCompactTransverse (d : ℕ) (a : ℝ) (T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)) :
    Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ)) :=
  {p | p.1 ∈ T ∧ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0}

theorem isCompact_packetCompactTransverse (d : ℕ) (a : ℝ) (ha : 0 < a)
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T)
    (ht : ∀ z ∈ T, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    IsCompact (packetCompactTransverse d a T) := by
  let f : (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ)) →
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ)) :=
    fun p => (p.1, OAI.Analysis.Calculus.Current.physicalFiberInverse a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2)
  have hf : ContinuousOn f (T ×ˢ OAI.Analysis.Calculus.Current.fiberParameterBall d) := by
    intro p hp
    have hc : Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ) =>
        (OAI.Analysis.PDE.Green.energyComplexTime p.1, p.2)) :=
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).continuous.comp continuous_fst).prodMk continuous_snd
    have hi : ContinuousAt (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ) =>
        OAI.Analysis.Calculus.Current.physicalFiberInverse a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2) p :=
      ((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2
        (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hp.2)).continuousAt).comp
          (f := fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ) =>
            (OAI.Analysis.PDE.Green.energyComplexTime p.1, p.2)) hc.continuousAt
    exact (continuousAt_fst.prodMk hi).continuousWithinAt
  have heq : f '' (T ×ˢ OAI.Analysis.Calculus.Current.fiberParameterBall d) = packetCompactTransverse d a T := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨hq.1, ?_⟩
      have hm : OAI.Analysis.Calculus.Current.physicalFiberInverse a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2 ∈
          OAI.Analysis.Calculus.Current.physicalFiberInverse a (OAI.Analysis.PDE.Green.energyComplexTime q.1) '' OAI.Analysis.Calculus.Current.fiberParameterBall d := ⟨q.2, hq.2, rfl⟩
      rw [OAI.Analysis.PDE.Green.physicalFiberInverse_image_closed_ball a (OAI.Analysis.PDE.Green.energyComplexTime q.1) ha (ht q.1 hq.1)] at hm
      exact hm
    · rintro ⟨hp, hq⟩
      have hm : p.2 ∈ OAI.Analysis.Calculus.Current.physicalFiberInverse a (OAI.Analysis.PDE.Green.energyComplexTime p.1) '' OAI.Analysis.Calculus.Current.fiberParameterBall d := by
        rw [OAI.Analysis.PDE.Green.physicalFiberInverse_image_closed_ball a (OAI.Analysis.PDE.Green.energyComplexTime p.1) ha (ht p.1 hp)]
        exact hq
      obtain ⟨v, hv, he⟩ := hm
      exact ⟨(p.1, v), ⟨hp, hv⟩, Prod.ext rfl he⟩
  rw [← heq]
  exact (hT.prod (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d)).image_of_continuousOn hf

/-- A locally smooth periodic packet admits a genuine smooth periodic
extension near each compact set of admissible closed fibers. The extension
is chosen after the compact time set, never across its degenerate boundary. -/
theorem exists_packet_local_extension {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {a : ℝ} (ha : 0 < a)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ} (hu : PacketLocalSmooth d a u)
    (hp : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x)
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T)
    (ht : ∀ z ∈ T, a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4) :
    ∃ g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ, ContDiff ℝ ∞ g ∧
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (fullPhysicalSplit d) (packetSpatialBasis R) g ∧
      ∀ x, OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ T → OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0 →
        g =ᶠ[𝓝 x] u := by
  obtain ⟨U, hU, hu, hcontains⟩ := hu
  have hCU (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hx : (fullPhysicalSplit d x).2 ∈ packetCompactTransverse d a T) : x ∈ U := by
    apply hcontains x
    · rw [fullPhysicalSplit_fullProjection]
      exact ht _ hx.1
    · change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1
        (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2 ≤ 0
      rw [fullPhysicalSplit_fullProjection]
      exact hx.2
  obtain ⟨g, hg, hgp, hgu⟩ := exists_smooth_lattice_extension_near
    (fullPhysicalSplit d) (packetSpatialBasis R)
    (isCompact_packetCompactTransverse d a ha hT (fun z hz => (ht z hz).1.le)) hU hCU u hu
    (latticePeriodic_full_of_cell_period c R hp)
  refine ⟨g, hg, hgp, ?_⟩
  intro x hx hr
  apply hgu
  refine ⟨?_, ?_⟩
  · simpa only [fullPhysicalSplit_snd_fst] using hx
  · change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1
      (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2 ≤ 0 at hr
    rwa [fullPhysicalSplit_fullProjection] at hr

end OAI.Analysis.PDE.Concentration
