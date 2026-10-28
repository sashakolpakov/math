import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationFiberConnected

/-! # Rational Fiber Connected -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalFiberConnected.Construction

noncomputable section

/-! Actual base change along a rational point has the topology of the corresponding scheme fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] {X B : Scheme.{u}} (f : X ⟶ B)
  (p : B ⟶ Spec (CommRingCat.of K)) [IsSeparated p]
  (b : Spec (CommRingCat.of K) ⟶ B) (hb : b ≫ p = 𝟙 _)

/-- A rational point is a closed immersion, so its actual pullback has exactly the topology
of the corresponding residue-field fiber. -/
def rationalPointPullbackHomeomorph :
    (pullback f b : Scheme.{u}) ≃ₜ f.fiber (b (IsLocalRing.closedPoint K)) := by
  have : IsClosedImmersion (b ≫ p) := by rw [hb]; infer_instance
  have : IsClosedImmersion b := IsClosedImmersion.of_comp b p
  have hr : Set.range b = {b (IsLocalRing.closedPoint K)} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg b (Subsingleton.elim z (IsLocalRing.closedPoint K))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint K, rfl⟩
  have hg : Set.range (pullback.fst f b) = f ⁻¹' {b (IsLocalRing.closedPoint K)} := by
    rw [Scheme.Pullback.range_fst, hr]
  exact (pullback.fst f b).isClosedEmbedding.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hg).trans (f.fiberHomeo (b (IsLocalRing.closedPoint K))).symm)

include hb in
/-- Connectedness of the actual fiber implies connectedness of the actual rational-point base change. -/
theorem rationalPoint_pullback_connected
    [ConnectedSpace (f.fiber (b (IsLocalRing.closedPoint K)))] :
    ConnectedSpace (pullback f b : Scheme.{u}) :=
  (rationalPointPullbackHomeomorph f p b hb).connectedSpace_iff.mpr inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalFiberConnected.Construction
