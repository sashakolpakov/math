import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Product Fixed Vectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFixedVectors.CM

noncomputable section

/-! The separate active and away stabilizers give fixed vectors for
their product subgroup. -/

variable {A B V : Type*} [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
  (ρ : A × B →* (V ≃ₗ[ℂ] V)) (v : V)

theorem fixed (a : A) (b : B) (ha : ρ (a, 1) v = v) (hb : ρ (1, b) v = v) :
    ρ (a, b) v = v := by
  have he : (a, b) = (a, (1 : B)) * ((1 : A), b) := by simp
  rw [he, map_mul, LinearEquiv.mul_apply, hb, ha]

def awayStabilizer [TopologicalSpace B] (h : IsOpen {b : B | ρ (1, b) v = v}) :
    OpenSubgroup B where
  toSubgroup := RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness.vectorStabilizer (ρ.comp (MonoidHom.inr A B)) v
  isOpen' := h

theorem away_mem [TopologicalSpace B] (h : IsOpen {b : B | ρ (1, b) v = v}) (b : B) :
    b ∈ awayStabilizer ρ v h ↔ ρ (1, b) v = v := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFixedVectors.CM
