import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sublevel
import OAI.Analysis.Calculus.SmoothExtension.ExtensionInfinityLocal

open Set Filter Module
open scoped Topology ContDiff Manifold
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Variational

section Periodic
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

theorem contDiff_discretePeriodization_infty (L : T →+ E)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (OAI.Analysis.PDE.Variational.discretePeriodization L φ) := by
  rw [contDiff_infty]
  intro q
  exact contDiff_discretePeriodization_order L hL (hφ.of_le (by simp)) hc

/-- The same compactly weighted average is smooth at every order and
periodic everywhere, while retaining the prescribed values on K. -/
theorem exists_smooth_periodic_extension_of_weight
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : ∀ x ∈ K, ∀ z, x + L z ∈ K)
    (u g ρ : E → ℝ) (hu : ∀ x ∈ K, ∀ z, u (x + L z) = u x)
    (hg : ContDiff ℝ ∞ g) (hgu : ∀ x ∈ K, g x = u x)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x ∈ K, ∃ z, ρ (x + L z) = 1) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      (∀ x z, f (x + L z) = f x) ∧ ∀ x ∈ K, f x = u x := by
  let D := OAI.Analysis.PDE.Variational.discretePeriodization L ρ
  let B := OAI.Analysis.PDE.Variational.discretePeriodization L (fun x ↦ ρ x * g x)
  have hDc : ContDiff ℝ ∞ D := contDiff_discretePeriodization_infty L hL hρ hρc
  have hBc : ContDiff ℝ ∞ B :=
    contDiff_discretePeriodization_infty L hL (hρ.mul hg) hρc.mul_right
  refine ⟨fun x ↦ smoothReciprocal (D x) * B x,
    (contDiff_smoothReciprocal.comp hDc).mul hBc, ?_, ?_⟩
  · intro x z
    simp only [D,B,OAI.Analysis.PDE.Variational.discretePeriodization_add]
  · intro x hx
    have hD1 : 1 ≤ D x := by
      obtain ⟨z,hz⟩ := hρ1 x hx
      rw [← hz]
      exact (summable_discrete_translates L hL hρc x).le_tsum z (fun j _ ↦ hρ0 _)
    have hB : B x = D x * u x := by
      calc
        B x = ∑' z, ρ (x + L z) * u x := by
          apply tsum_congr
          intro z
          change ρ (x + L z) * g (x + L z) = _
          rw [hgu _ (hK x hx z),hu x hx z]
        _ = D x * u x := by rw [tsum_mul_right]; rfl
    change smoothReciprocal (D x) * B x = u x
    rw [hB,← mul_assoc,smoothReciprocal_mul hD1,one_mul]

theorem exists_smooth_periodic_extension_of_local_on [FiniteDimensional ℝ E]
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K C : Set E} (hK : IsClosed K) (hC : IsCompact C)
    (hKper : ∀ x ∈ K, ∀ z, x + L z ∈ K)
    (hcover : ∀ x ∈ K, ∃ z, x + L z ∈ C)
    (u : E → ℝ) (huper : ∀ x ∈ K, ∀ z, u (x + L z) = u x)
    (hl : ∀ x ∈ K, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ K ∩ U, g y = u y) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x z, g (x + L z) = g x) ∧ ∀ x ∈ K, g x = u x := by
  obtain ⟨g,hg,hgu⟩ := exists_smooth_extension_of_local_on hK u hl
  obtain ⟨ρ,hρ,hρc,hρ0,hρ1⟩ := exists_smooth_compact_one_on_compact hC
  apply exists_smooth_periodic_extension_of_weight L hL hKper u g ρ huper hg hgu
    hρ hρc hρ0
  intro x hx
  obtain ⟨z,hz⟩ := hcover x hx
  exact ⟨z,hρ1 _ hz⟩
end Periodic

section Lattice
variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_latticePeriodic_smooth_extension_of_local_on
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K C : Set E} (hK : IsClosed K) (hC : IsCompact C)
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    (hrep : ∀ x ∈ K, OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x ∈ C)
    (u : E → ℝ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hl : ∀ x ∈ K, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ K ∩ U, g y = u y) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧ ∀ x ∈ K, g x = u x := by
  have hshift (x : E) (z : Submodule.span ℤ (Set.range b)) :
      x + latticeShiftHom e b z = e.symm ((e x).1 + (z : P),(e x).2) := by
    change x + e.symm ((z : P),0) = _
    simpa only [add_comm] using (OAI.Analysis.PDE.Dirichlet.lattice_translate_eq e x (z : P)).symm
  have hcover : ∀ x ∈ K, ∃ z, x + latticeShiftHom e b z ∈ C := by
    intro x hx
    refine ⟨-ZSpan.floor b (e x).1,?_⟩
    rw [hshift]
    simpa only [OAI.Analysis.PDE.Dirichlet.latticeRepresentative,ZSpan.fract_apply,Submodule.coe_neg,sub_eq_add_neg]
      using hrep x hx
  obtain ⟨g,hg,hgp,hgK⟩ := exists_smooth_periodic_extension_of_local_on
    (latticeShiftHom e b) (finite_latticeShiftHom_norm e b) hK hC
    (fun x hx z ↦ by rw [hshift]; exact Eq.mpr (hKper x z) hx)
    hcover u (fun x _ z ↦ by rw [hshift]; exact huper x z) hl
  refine ⟨g,hg,?_,hgK⟩
  intro x z
  rw [← hshift]
  exact hgp x z

/-- Smooth local representatives on a periodic closed sublevel yield one
globally smooth periodic representative, with exactly the same values. -/
theorem exists_latticePeriodic_smooth_sublevel_extension_on
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (u : E → ℝ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hl : ∀ x, r x ≤ 0 → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ U, r y ≤ 0 → g y = u y) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀ x, r x ≤ 0 → g x = u x := by
  apply exists_latticePeriodic_smooth_extension_of_local_on e b
    (isClosed_le hr continuous_const) (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hC hr)
    (hrper.comp (fun t ↦ t ≤ 0))
    (fun x hx ↦ OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrper hbounded hx) u huper
  intro x hx
  obtain ⟨U,hU,hxU,g,hg,hgu⟩ := hl x hx
  exact ⟨U,hU,hxU,g,hg,fun y hy ↦ hgu y hy.2 hy.1⟩
end Lattice
end OAI.Analysis.Calculus.SmoothExtension
