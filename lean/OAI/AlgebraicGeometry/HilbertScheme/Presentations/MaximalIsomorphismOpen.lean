import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OnOpenBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RestrictedIsomorphismStalks

/-! # Maximal Isomorphism Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIsomorphismOpen

noncomputable section

/-! Every scheme morphism has a largest target open over which it is
an isomorphism, and its restriction to that open is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def maximalIsomorphismOpen : Y.Opens :=
  ⨆ (U : Y.Opens) (_ : IsIso (f ∣_ U)), U

theorem mem_maximalIsomorphismOpen (y : Y) :
    y ∈ maximalIsomorphismOpen f ↔ ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  simp only [maximalIsomorphismOpen, TopologicalSpace.Opens.mem_iSup]
  exact ⟨fun ⟨U, hi, hy⟩ => ⟨U, hy, hi⟩, fun ⟨U, hy, hi⟩ => ⟨U, hi, hy⟩⟩

theorem maximalIsomorphismOpen_restrict_isIso :
    IsIso (f ∣_ maximalIsomorphismOpen f) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨U, hy, hi⟩ := (mem_maximalIsomorphismOpen f y.val).mp y.property
  let := hi
  let V := (maximalIsomorphismOpen f).ι ⁻¹ᵁ U
  refine ⟨V, hy, ?_⟩
  change IsIso ((f ∣_ maximalIsomorphismOpen f) ∣_ V)
  rw [← OpenPullbackIsomorphismTransport.isIso_pullback_fst_open_iff, RestrictedIsomorphismStalks.isIso_pullback_restrict_iff]
  apply OnOpenBaseChange.isIso_pullback_fst_of_range_subset_isomorphism_open f U
  rintro z ⟨t, rfl⟩
  exact t.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIsomorphismOpen
