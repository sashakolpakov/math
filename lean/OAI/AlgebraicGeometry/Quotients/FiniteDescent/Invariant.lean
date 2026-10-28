import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Invariant -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Invariant.Construction.InvariantCore

/-!
# Invariant cores of open subsets

For a finite equivalence relation, removing every orbit meeting the complement
of an open gives its largest invariant open subset. The relation on underlying
points is established using actual scheme pullbacks.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R X : Scheme.{u}} (s t : R ⟶ X)

/-- Two points are related when a point of the relation maps to them. -/
def Related (x y : X) : Prop := ∃ r : R, s r = x ∧ t r = y

variable {s t} (e : CategoryTheory.EquivalenceRelation s t)

include e in
theorem related_refl (x : X) : Related s t x x := by
  exact ⟨e.r x, congrArg (fun f => f x) e.reflexivity₁,
    congrArg (fun f => f x) e.reflexivity₂⟩

include e in
theorem related_symm {x y : X} (h : Related s t x y) : Related s t y x := by
  obtain ⟨r, hs, ht⟩ := h
  refine ⟨e.s r, ?_, ?_⟩
  · simpa only [← Scheme.Hom.comp_apply, e.symmetry₁] using ht
  · simpa only [← Scheme.Hom.comp_apply, e.symmetry₂] using hs

include e in
theorem related_trans {x y z : X} (hxy : Related s t x y) (hyz : Related s t y z) :
    Related s t x z := by
  obtain ⟨r, hr, hr'⟩ := hxy
  obtain ⟨r', hr'', hr'''⟩ := hyz
  have hc : IsPullback e.c.fst e.c.snd t s := IsPullback.of_isLimit e.isLimit
  obtain ⟨a, ha, ha'⟩ := Scheme.exists_preimage_of_isPullback hc r r' (hr'.trans hr''.symm)
  refine ⟨e.t a, ?_, ?_⟩
  · exact (congrArg (fun f => f a) e.transitivity₁).trans ((congrArg s ha).trans hr)
  · exact (congrArg (fun f => f a) e.transitivity₂).trans ((congrArg t ha').trans hr''')

variable (s t) [IsFinite s]

/-- Every orbit of a finite relation is finite. -/
theorem finite_orbit (x : X) : {y : X | Related s t x y}.Finite := by
  simpa only [Related, Set.mem_preimage, Set.mem_singleton_iff, Set.image, Set.ofPred_mem_eq]
    using (s.finite_preimage_singleton x).image t

/-- The largest invariant open inside an open set: remove all points related
to a point outside that open. -/
def core (U : X.Opens) : X.Opens :=
  ⟨(s '' (t ⁻¹' (U : Set X)ᶜ))ᶜ,
    (s.isClosedMap _ (U.isOpen.isClosed_compl.preimage t.continuous)).isOpen_compl⟩

theorem mem_core (U : X.Opens) (x : X) :
    x ∈ core s t U ↔ ∀ y, Related s t x y → y ∈ U := by
  constructor
  · intro h y hy
    obtain ⟨r, hr, hr'⟩ := hy
    by_contra hn
    exact h ⟨r, fun hrU => hn (hr' ▸ hrU), hr⟩
  · intro h hx
    obtain ⟨r, hr, hr'⟩ := hx
    exact hr (h (t r) ⟨r, hr', rfl⟩)

include e in
theorem core_le (U : X.Opens) : core s t U ≤ U := fun x hx =>
  (mem_core s t U x).mp hx x (related_refl e x)

include e in
theorem core_invariant (U : X.Opens) : s ⁻¹ᵁ core s t U = t ⁻¹ᵁ core s t U := by
  ext r
  change s r ∈ core s t U ↔ t r ∈ core s t U
  rw [mem_core, mem_core]
  have hst : Related s t (s r) (t r) := ⟨r, rfl, rfl⟩
  exact ⟨fun h y hy => h y (related_trans e hst hy),
    fun h y hy => h y (related_trans e (related_symm e hst) hy)⟩

/-- Every invariant open contained in `U` is contained in its invariant core. -/
theorem le_core (U V : X.Opens) (hV : s ⁻¹ᵁ V = t ⁻¹ᵁ V) (hVU : V ≤ U) :
    V ≤ core s t U := by
  intro x hx
  apply (mem_core s t U x).mpr
  intro y hy
  obtain ⟨r, hr, hr'⟩ := hy
  have h : r ∈ s ⁻¹ᵁ V := by simpa only [Scheme.Hom.mem_preimage, hr] using hx
  rw [hV] at h
  exact hVU (by simpa only [Scheme.Hom.mem_preimage, hr'] using h)

include e in
/-- An orbit contained in an open neighborhood remains in its invariant
core; taking the core loses no point of that orbit. -/
theorem orbit_subset_core (U : X.Opens) (x : X)
    (hU : ∀ y, Related s t x y → y ∈ U) :
    ∀ y, Related s t x y → y ∈ core s t U := by
  intro y hxy
  exact (mem_core s t U y).mpr fun z hyz => hU z (related_trans e hxy hyz)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Invariant.Construction.InvariantCore
