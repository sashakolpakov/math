import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso

/-! # Tail Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.TailQuasiIso

noncomputable section

/-! A cochain map which is an isomorphism in degree zero and a
quasi-isomorphism after deleting degree zero is a quasi-isomorphism. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [Ring R]
  (K : CochainComplex (ModuleCat.{v} R) ℕ)

def tail : CochainComplex (ModuleCat.{v} R) ℕ where
  X n := K.X (n + 1)
  d i j := K.d (i + 1) (j + 1)
  shape i j h := K.shape _ _ (by simpa only [ComplexShape.up_Rel, Nat.add_right_cancel_iff] using h)
  d_comp_d' i j k _ _ := K.d_comp_d _ _ _

@[simp] theorem tail_d (n : ℕ) : (tail K).d n (n + 1) = K.d (n + 1) (n + 2) := rfl

variable {K} {L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)

def map : tail K ⟶ tail L where
  f n := f.f (n + 1)
  comm' i j _ := f.comm (i + 1) (j + 1)

@[simp] theorem map_f (n : ℕ) : (map f).f n = f.f (n + 1) := rfl

private theorem zero_cycle_injective (hf : QuasiIso (map f))
    (x : K.X 1) (hx : K.d 1 2 x = 0) (hfx : f.f 1 x = 0) : x = 0 := by
  obtain ⟨z, hz⟩ := AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex.boundary_reflection_of_quasiIso (map f) hf 0 x
    (by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hx) ⟨0, by simpa [map_f, tail] using hfx.symm⟩
  have hd := K.shape 1 1 (by simp)
  simpa only [tail, Nat.pred_zero, Nat.reduceAdd, hd, ModuleCat.hom_zero, LinearMap.zero_apply] using hz.symm

private theorem zero_cycle_surjective (hf : QuasiIso (map f))
    (y : L.X 1) (hy : L.d 1 2 y = 0) :
    ∃ x : K.X 1, K.d 1 2 x = 0 ∧ f.f 1 x = y := by
  obtain ⟨x, hx, z, hz⟩ := AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex.cycle_lift_of_quasiIso (map f) hf 0 y
    (by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hy)
  refine ⟨x, by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hx, ?_⟩
  have hd := L.shape 1 1 (by simp)
  have h : (0 : L.X 1) = f.f 1 x - y := by
    simpa only [tail, Nat.pred_zero, Nat.reduceAdd, hd, ModuleCat.hom_zero, LinearMap.zero_apply, map_f] using hz
  exact sub_eq_zero.mp h.symm

theorem quasiIso [IsIso (f.f 0)] (hf : QuasiIso (map f)) : QuasiIso f := by
  have hzero : Function.Bijective (f.f 0) := (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso.DoubleComplex.quasiIso_of_cycle_lift_and_boundary_reflection
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by cases n <;> simp
    rw [hp, CochainComplex.next]
    intro y hy
    cases n with
    | zero =>
      obtain ⟨x, hxy⟩ := hzero.surjective y
      refine ⟨x, ?_, 0, ?_⟩
      · apply zero_cycle_injective f hf (K.d 0 1 x)
        · exact ConcreteCategory.congr_hom (K.d_comp_d 0 1 2) x
        · have h := ConcreteCategory.congr_hom (f.comm 0 1) x
          change L.d 0 1 (f.f 0 x) = f.f 1 (K.d 0 1 x) at h
          exact h.symm.trans (by rw [hxy]; exact hy)
      · simp only [map_zero, hxy, sub_self]
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨x, hx, hxy⟩ := zero_cycle_surjective f hf y hy
        exact ⟨x, hx, 0, by simp only [map_zero, hxy, sub_self]⟩
      | succ n =>
        obtain ⟨x, hx, z, hz⟩ := AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex.cycle_lift_of_quasiIso (map f) hf (n + 1) y
          (by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hy)
        exact ⟨x, by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hx, z,
          by simpa only [tail, Nat.pred_succ, map_f, Nat.reduceAdd, Nat.add_assoc] using hz⟩
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by cases n <;> simp
    rw [hp, CochainComplex.next]
    intro x hx hb
    cases n with
    | zero =>
      obtain ⟨z, hz⟩ := hb
      have hd := L.shape 0 0 (by simp)
      have hfx : f.f 0 x = 0 := by
        simpa only [tail, Nat.pred_zero, Nat.reduceAdd, hd, ModuleCat.hom_zero, LinearMap.zero_apply] using hz.symm
      have hx0 : x = 0 := hzero.injective (hfx.trans (map_zero _).symm)
      exact ⟨0, by simp only [map_zero, hx0]⟩
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨y, hy⟩ := hb
        change K.d 1 2 x = 0 at hx
        change L.d 0 1 y = f.f 1 x at hy
        obtain ⟨z, hz⟩ := hzero.surjective y
        refine ⟨z, ?_⟩
        have he : x - K.d 0 1 z = 0 := by
          apply zero_cycle_injective f hf
          · rw [map_sub, hx]
            have hd := ConcreteCategory.congr_hom (K.d_comp_d 0 1 2) z
            change K.d 1 2 (K.d 0 1 z) = 0 at hd
            rw [hd, sub_self]
          · rw [map_sub]
            have hc := ConcreteCategory.congr_hom (f.comm 0 1) z
            change L.d 0 1 (f.f 0 z) = f.f 1 (K.d 0 1 z) at hc
            rw [← hc, hz, hy, sub_self]
        exact (sub_eq_zero.mp he).symm
      | succ n =>
        obtain ⟨z, hz⟩ := AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativePrimitive.DoubleComplex.boundary_reflection_of_quasiIso (map f) hf (n + 1) x
          (by simpa only [tail, Nat.reduceAdd, Nat.add_assoc] using hx)
          (by simpa only [tail, Nat.pred_succ, map_f, Nat.reduceAdd, Nat.add_assoc] using hb)
        exact ⟨z, by simpa only [tail, Nat.pred_succ, Nat.reduceAdd, Nat.add_assoc] using hz⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.TailQuasiIso
