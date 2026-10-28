import OAI.Geometry.ComplexTorus.RiemannProjectivity.IdentityEq
import Mathlib.Topology.Irreducible

/-! # Analytic Irreducibility Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility

noncomputable section

/-!
# RiemannProjectivity: irreducibility detected by local holomorphic equations

A subset of a complex vector space given locally by holomorphic equations
has closed interior. Thus, on the connected vector space, a nonempty open
part forces the whole subset. This applies to arbitrary families of local
equations and will be used for pullbacks of Zariski closed sets.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def HasLocalEquations (S : Set V) (x : V) : Prop :=
  ∃ U : Set V, IsOpen U ∧ x ∈ U ∧ ∃ F : Set (V → ℂ),
    (∀ f ∈ F, DifferentiableOn ℂ f U) ∧
    ∀ y ∈ U, y ∈ S ↔ ∀ f ∈ F, f y = 0

theorem isClosed_of_local_equations {S : Set V}
    (hlocal : ∀ x, HasLocalEquations S x) : IsClosed S := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, hU, hxU, F, hF, heq⟩ := hlocal x
  have hne : ∃ f ∈ F, f x ≠ 0 := by
    change ¬x ∈ S at hx
    simpa only [heq x hxU, not_forall, exists_prop] using hx
  obtain ⟨f, hf, hfx⟩ := hne
  have hfcont := ((hF f hf).continuousOn.continuousAt (hU.mem_nhds hxU))
  filter_upwards [hU.mem_nhds hxU, hfcont.eventually_ne hfx] with y hy hfy
  exact fun hys => hfy ((heq y hy).mp hys f hf)

theorem mem_interior_of_local_equations {S : Set V} {x : V}
    (hlocal : HasLocalEquations S x) (hx : x ∈ closure (interior S)) : x ∈ interior S := by
  obtain ⟨U, hU, hxU, F, hF, heq⟩ := hlocal
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hx r hr
  have hyball : y ∈ ball x r := by simpa only [mem_ball, dist_comm] using hyx
  have hballS : ball x r ⊆ S := by
    intro z hz
    apply (heq z (hball hz)).mpr
    intro f hf
    have hzero : ∀ᶠ w in 𝓝 y, f w = 0 := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hy,
        isOpen_ball.mem_nhds hyball] with w hw hwball
      exact (heq w (hball hwball)).mp hw f hf
    exact IdentityEq.Constructions.Identity.eq_zero_of_zero_germ isOpen_ball (convex_ball x r).isPreconnected
      ((hF f hf).mono hball) hyball hzero z hz
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (ball_mem_nhds x hr) hballS)

theorem isClosed_interior_of_local_equations {S : Set V}
    (hlocal : ∀ x, HasLocalEquations S x) : IsClosed (interior S) :=
  isClosed_of_closure_subset (fun x hx => mem_interior_of_local_equations (hlocal x) hx)

theorem eq_univ_of_interior_nonempty {S : Set V}
    (hlocal : ∀ x, HasLocalEquations S x) (hne : (interior S).Nonempty) : S = univ := by
  have hcl : IsClopen (interior S) :=
    ⟨isClosed_interior_of_local_equations hlocal, isOpen_interior⟩
  rcases isClopen_iff.mp hcl with h | h
  · exact (hne.ne_empty h).elim
  · exact eq_univ_of_univ_subset (h ▸ interior_subset)

/-- A parametrized image is Zariski irreducible whenever every closed-set
pullback is locally the common zero locus of holomorphic functions. -/
theorem isIrreducible_range {X : Type*} [TopologicalSpace X] (f : V → X)
    (heq : ∀ Z : Set X, IsClosed Z → ∀ x, HasLocalEquations (f ⁻¹' Z) x) :
    IsIrreducible (range f) := by
  refine ⟨range_nonempty f, isPreirreducible_iff_isClosed_union_isClosed.mpr ?_⟩
  intro A B hA hB hcover
  by_cases hfull : range f ⊆ B
  · exact Or.inr hfull
  · left
    obtain ⟨y, ⟨x, rfl⟩, hx⟩ := not_subset.mp hfull
    have hBclosed := isClosed_of_local_equations (heq B hB)
    have hBA : (f ⁻¹' B)ᶜ ⊆ f ⁻¹' A := by
      intro z hz
      exact (hcover ⟨z, rfl⟩).resolve_right hz
    have hxint : x ∈ interior (f ⁻¹' B)ᶜ := by
      rw [hBclosed.isOpen_compl.interior_eq]
      exact hx
    have hne : (interior (f ⁻¹' A)).Nonempty := ⟨x, interior_mono hBA hxint⟩
    have hfullA := eq_univ_of_interior_nonempty (heq A hA) hne
    rintro _ ⟨z, rfl⟩
    exact show z ∈ f ⁻¹' A from hfullA ▸ mem_univ z

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility
