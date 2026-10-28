import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

/-! # Cochain Boundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainBoundary

noncomputable section

/-! Subtracting an actual cochain boundary preserves the original homology class. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{v} R) ℕ)

def subBoundary (n : ℕ) (x : CochainClasses.cycles K (n + 1)) (z : K.X n) : CochainClasses.cycles K (n + 1) :=
  ⟨x.val - K.d n (n + 1) z, by
    change K.d (n + 1) (n + 1 + 1) (x.val - K.d n (n + 1) z) = 0
    rw [map_sub, x.property]
    have h := congrArg (fun f => f z) (K.d_comp_d n (n + 1) (n + 1 + 1))
    change K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) z) = 0 at h
    rw [h, sub_self]⟩

theorem class_eq (n : ℕ) (x : CochainClasses.cycles K (n + 1)) (z : K.X n) :
    CochainClasses.classMap K (n + 1) (subBoundary K n x z) = CochainClasses.classMap K (n + 1) x := by
  symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (CochainClasses.classMap_succ_eq_zero_iff K n (x - subBoundary K n x z)).mpr
  exact ⟨z, by change _ = x.val - (x.val - _); abel⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainBoundary
