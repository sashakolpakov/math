import Mathlib

/-! # Split Linear Topology -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitLinearTopology.Realization

noncomputable section

/-! A continuous linear projection with a continuous section splits topologically. -/

open scoped Classical

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℚ A] [Module ℚ B]

def splitLinearEquiv (P : A →ₗ[ℚ] B) (I : B →ₗ[ℚ] A) (hPI : ∀ b, P (I b) = b) :
    A ≃ₗ[ℚ] B × LinearMap.ker P where
  toFun a := (P a, ⟨a - I (P a), by rw [LinearMap.mem_ker, map_sub, hPI, sub_self]⟩)
  invFun p := I p.1 + p.2.val
  left_inv a := by dsimp; abel
  right_inv p := by
    have hp : P p.2.val = 0 := p.2.property
    apply Prod.ext
    · change P (I p.1 + p.2.val) = p.1
      rw [map_add, hPI, hp, add_zero]
    · apply Subtype.ext
      change I p.1 + p.2.val - I (P (I p.1 + p.2.val)) = p.2.val
      rw [map_add, hPI, hp, add_zero]
      abel
  map_add' a b := by
    apply Prod.ext
    · exact map_add P a b
    · apply Subtype.ext
      change (a + b) - I (P (a + b)) = (a - I (P a)) + (b - I (P b))
      rw [map_add, map_add]
      abel
  map_smul' c a := by
    apply Prod.ext
    · exact map_smul P c a
    · apply Subtype.ext
      change c • a - I (P (c • a)) = c • (a - I (P a))
      rw [map_smul, map_smul, smul_sub]

def splitLinearHomeomorph
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    (P : A →ₗ[ℚ] B) (I : B →ₗ[ℚ] A) (hPI : ∀ b, P (I b) = b)
    (hP : Continuous P) (hI : Continuous I) : A ≃ₜ B × LinearMap.ker P where
  toEquiv := (splitLinearEquiv P I hPI).toEquiv
  continuous_toFun := hP.prodMk ((continuous_id.sub (hI.comp hP)).subtype_mk _)
  continuous_invFun := (hI.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitLinearTopology.Realization
