import Mathlib

/-! # Covariant Orbit -/

namespace OAI.RepresentationTheory.Theta.Adelic.CovariantOrbit

noncomputable section

/-! Orbit equivalence for tensors described by their covariant evaluation
law. Both the base action and the variable and scalar cocycles are explicit. -/

variable {G X Y V : Type*} [Group G] [MulAction G X]
variable (Γ : Subgroup G) (e : Y → V → ℂ)
variable (u : G → X → V → V) (c : G → X → ℂ)
variable (u_one : ∀ x v, u 1 x v = v)
variable (u_mul : ∀ g h x v, u (g * h) x v = u g (h • x) (u h x v))
variable (c_one : ∀ x, c 1 x = 1)
variable (c_mul : ∀ g h x, c (g * h) x = c g (h • x) * c h x)

def covariantOrbit (p q : X × Y) : Prop :=
  ∃ g ∈ Γ, g • p.1 = q.1 ∧ ∀ v, e q.2 (u g p.1 v) = c g p.1 * e p.2 v

include u_one u_mul c_one c_mul in
theorem covariantOrbit_equivalence :
    Equivalence (covariantOrbit Γ e u c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨1, Γ.one_mem, one_smul _ _, fun v => by rw [u_one, c_one, one_mul]⟩
  · rintro p q ⟨g, hg, hbase, ht⟩
    refine ⟨g⁻¹, Γ.inv_mem hg, ?_, ?_⟩
    · rw [← hbase, inv_smul_smul]
    · intro v
      have hu : u g p.1 (u g⁻¹ q.1 v) = v := by
        have hh := u_mul g g⁻¹ q.1 v
        rw [mul_inv_cancel, u_one] at hh
        rw [← hbase, inv_smul_smul] at hh
        rw [hbase] at hh
        exact hh.symm
      have hc : c g⁻¹ q.1 * c g p.1 = 1 := by
        have hh := c_mul g⁻¹ g p.1
        rw [inv_mul_cancel, c_one, hbase] at hh
        exact hh.symm
      have hh := ht (u g⁻¹ q.1 v)
      rw [hu] at hh
      rw [hh, ← mul_assoc, hc, one_mul]
  · rintro p q r ⟨g, hg, hbase, ht⟩ ⟨h, hh, hbase', ht'⟩
    refine ⟨h * g, Γ.mul_mem hh hg, ?_, ?_⟩
    · rw [mul_smul, hbase, hbase']
    · intro v
      rw [u_mul, hbase, ht', ht, c_mul, hbase, mul_assoc]

def covariantOrbitSetoid : Setoid (X × Y) where
  r := covariantOrbit Γ e u c
  iseqv := covariantOrbit_equivalence Γ e u c u_one u_mul c_one c_mul

end

end OAI.RepresentationTheory.Theta.Adelic.CovariantOrbit
