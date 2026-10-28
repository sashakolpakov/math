import OAI.Analysis.Fourier.WavePackets.Dirichlet.FamilyBarriers

noncomputable section
open Set Module
open scoped Topology ContDiff
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet

variable {m : ℕ} {P V ι Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [TopologicalSpace Z]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

/-- A moving closure chart constructs the compact family of physical
representatives. The reverse chart fixes the periodic coordinates, as does
the actual padded physical transport. -/
theorem compact_closure_family_of_transport
    (D₀ : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    (D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    {U L : Set Z} (hL : IsCompact L) (hLU : L ⊆ U)
    (Φ Ψ : Z → E → E)
    (hΦ : ContinuousOn (fun p : Z × E => Φ p.1 p.2)
      (U ×ˢ {x | D₀.defining x ≤ 0}))
    (hforward : ∀ z ∈ U, ∀ x, D₀.defining x ≤ 0 → (D z).defining (Φ z x) ≤ 0)
    (hbackward : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 → D₀.defining (Ψ z x) ≤ 0)
    (hinverse : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 → Φ z (Ψ z x) = x)
    (hperiodic : ∀ z ∈ U, ∀ x, (e (Ψ z x)).1 = (e x).1) :
    ∃ C : Set (Z × E), IsCompact C ∧
      C ⊆ {p | p.1 ∈ U ∧ (D p.1).defining p.2 ≤ 0} ∧
      ∀ z ∈ L, ∀ x, (D z).defining x ≤ 0 → (z,OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x) ∈ C := by
  let S := OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b D₀.transverse D₀.defining
  have hS : IsCompact S :=
    OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b D₀.compact D₀.defining_smooth.continuous
  let T : Z × E → Z × E := fun p => (p.1,Φ p.1 p.2)
  have hT : ContinuousOn T (L ×ˢ S) :=
    continuous_fst.continuousOn.prodMk (hΦ.mono (fun p hp => ⟨hLU hp.1,hp.2.2⟩))
  refine ⟨T '' (L ×ˢ S),(hL.prod hS).image_of_continuousOn hT,?_,?_⟩
  · rintro _ ⟨⟨z,x⟩,⟨hz,hx⟩,rfl⟩
    exact ⟨hLU hz,hforward z (hLU hz) x hx.2⟩
  · intro z hz x hx
    let y := OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x
    have hy : (D z).defining y ≤ 0 := by
      dsimp only [y]
      rwa [(D z).defining_periodic.representative]
    have hx₀ := hbackward z (hLU hz) y hy
    have hcell : Ψ z y ∈ S := by
      refine ⟨⟨e (Ψ z y),⟨?_,D₀.bounded _ hx₀⟩,e.symm_apply_apply _⟩,hx₀⟩
      rw [hperiodic z (hLU hz) y]
      change (e (e.symm (ZSpan.fract b (e x).1,(e x).2))).1 ∈ parallelepiped b
      rw [e.apply_symm_apply]
      exact ZSpan.fundamentalDomain_subset_parallelepiped b
        (ZSpan.fract_mem_fundamentalDomain b (e x).1)
    refine ⟨(z,Ψ z y),⟨hz,hcell⟩,?_⟩
    exact Prod.ext rfl (hinverse z (hLU hz) y hy)

/-- Uniform barriers for varying data on closures transported from a fixed
compact quotient. The compact set and the representative covering are
constructed from the actual maps, not supplied as separate assumptions. -/
theorem uniform_barriers_of_closure_transport
    (D₀ : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    (D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b)
    {U L : Set Z} (hL : IsCompact L) (hLU : L ⊆ U)
    (Φ Ψ : Z → E → E)
    (hΦ : ContinuousOn (fun p : Z × E => Φ p.1 p.2)
      (U ×ˢ {x | D₀.defining x ≤ 0}))
    (hforward : ∀ z ∈ U, ∀ x, D₀.defining x ≤ 0 → (D z).defining (Φ z x) ≤ 0)
    (hbackward : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 → D₀.defining (Ψ z x) ≤ 0)
    (hinverse : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 → Φ z (Ψ z x) = x)
    (hperiodic : ∀ z ∈ U, ∀ x, (e (Ψ z x)).1 = (e x).1)
    (hA : ContinuousOn (fun p : Z × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).background p.2)
      {p | p.1 ∈ U ∧ (D p.1).defining p.2 ≤ 0})
    (hR : ContinuousOn (fun p : Z × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).defining p.2)
      {p | p.1 ∈ U ∧ (D p.1).defining p.2 ≤ 0})
    (hF : ContinuousOn (fun p : Z × E => (D p.1).density p.2)
      {p | p.1 ∈ U ∧ (D p.1).defining p.2 ≤ 0}) :
    ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ z ∈ L, ∀ S : PeriodicQuaternionicSolution (D z),
      ∀ x, (D z).defining x ≤ 0 →
        B*(D z).defining x ≤ S.u x ∧ S.u x ≤ c*(D z).defining x := by
  obtain ⟨C,hC,hCD,hcover⟩ := compact_closure_family_of_transport D₀ D hL hLU
    Φ Ψ hΦ hforward hbackward hinverse hperiodic
  exact uniform_periodic_dirichlet_family_barriers D hC (fun p hp => (hCD hp).2)
    hcover (hA.mono hCD) (hR.mono hCD) (hF.mono hCD)

end OAI.Analysis.Fourier.WavePackets
