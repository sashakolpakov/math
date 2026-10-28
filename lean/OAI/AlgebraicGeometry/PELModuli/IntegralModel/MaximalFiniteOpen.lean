import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PullbackTransport

/-! # Maximal Finite Open -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.MaximalFiniteOpen

noncomputable section

/-! Every scheme morphism has a largest target open over which it is
finite. The finite locus is proved finite using target-locality. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def maximalFiniteOpen : Y.Opens := ⨆ (U : Y.Opens) (_ : IsFinite (f ∣_ U)), U

theorem mem_maximalFiniteOpen (y : Y) :
    y ∈ maximalFiniteOpen f ↔ ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) := by
  simp only [maximalFiniteOpen, TopologicalSpace.Opens.mem_iSup]
  exact ⟨fun ⟨U, h, hy⟩ => ⟨U, hy, h⟩, fun ⟨U, hy, h⟩ => ⟨U, h, hy⟩⟩

theorem maximalFiniteOpen_restrict_isFinite : IsFinite (f ∣_ maximalFiniteOpen f) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro y
  obtain ⟨U, hy, hU⟩ := (mem_maximalFiniteOpen f y.val).mp y.property
  let := hU
  let W := maximalFiniteOpen f
  let V := W.ι ⁻¹ᵁ U
  refine ⟨V, hy, ?_⟩
  let H := (isPullback_morphismRestrict (f ∣_ W) V).paste_vert (isPullback_morphismRestrict f W)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) H.isoPullback.inv,
    H.isoPullback_inv_fst]
  apply Finite.PullbackTransport.finite_pullback_fst_of_range_subset_open f U
  rintro z ⟨t, rfl⟩
  exact t.property

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.MaximalFiniteOpen
