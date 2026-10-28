import OAI.RepresentationTheory.Theta.Adelic.TensorProjective
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryFormHomeomorph

/-! # Representation Open Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RepresentationOpenLevel.CM

noncomputable section

/-! Actual open vector stabilizers and their transport through a
continuous group equivalence. -/

variable {G H V : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [AddCommGroup V] [Module ℂ V]
  (ρ : G →* (V ≃ₗ[ℂ] V)) (hρ : ∀ v : V, IsOpen {g | ρ g v = v})

def stabilizer (v : V) : OpenSubgroup G :=
  ⟨RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness.vectorStabilizer ρ v, hρ v⟩

def transport (e : G ≃ₜ* H) (v : V) : OpenSubgroup H :=
  (stabilizer ρ hρ v).comap e.symm.toMulEquiv.toMonoidHom e.symm.continuous

theorem transport_mem (e : G ≃ₜ* H) (v : V) (g : H) :
    g ∈ transport ρ hρ e v ↔ ρ (e.symm g) v = v := Iff.rfl

theorem image_mem (e : G ≃ₜ* H) (v : V) (g : G) :
    e g ∈ transport ρ hρ e v ↔ ρ g v = v := by
  rw [transport_mem, e.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RepresentationOpenLevel.CM
