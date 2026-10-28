import Mathlib.Data.Finset.NoncommProd
import Mathlib.Algebra.Group.Units.Equiv

/-! # Commuting Orbit Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CommutingOrbitNorm

noncomputable section

/-! The product of a commuting orbit of a finite group is fixed by
the group action, even when the ambient group is noncommutative. -/

open scoped Classical

theorem univ_noncommProd_equiv {ι M : Type*} [Fintype ι] [Monoid M]
    (e : ι ≃ ι) (f : ι → M) (hc : ∀ a b, Commute (f a) (f b)) :
    Finset.univ.noncommProd (fun a => f (e a)) (fun _ _ _ _ _ => hc _ _) =
      Finset.univ.noncommProd f (fun _ _ _ _ _ => hc _ _) := by
  unfold Finset.noncommProd
  have he : Finset.univ.val.map (fun a => f (e a)) = Finset.univ.val.map f := by
    change Finset.univ.val.map (f ∘ e) = Finset.univ.val.map f
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  congr 1

variable {A G : Type*} [Group A] [Fintype A] [Monoid G]

def commutingOrbitNorm (ρ : A →* Monoid.End G) (x : G)
    (hc : ∀ a b, Commute (ρ a x) (ρ b x)) : G :=
  Finset.univ.noncommProd (fun a => ρ a x) (fun _ _ _ _ _ => hc _ _)

theorem commutingOrbitNorm_fixed (ρ : A →* Monoid.End G) (x : G)
    (hc : ∀ a b, Commute (ρ a x) (ρ b x)) (a : A) :
    ρ a (commutingOrbitNorm ρ x hc) = commutingOrbitNorm ρ x hc := by
  have he (b : A) : ρ a (ρ b x) = ρ (a * b) x := by
    rw [map_mul]
    rfl
  have hm := Finset.map_noncommProd Finset.univ (fun b => ρ b x)
    (fun _ _ _ _ _ => hc _ _) (ρ a)
  have hp := Finset.noncommProd_congr (s₁ := (Finset.univ : Finset A)) rfl
    (fun b _ => he b) (fun _ _ _ _ _ => (hc _ _).map (ρ a))
  exact hm.trans (hp.trans (univ_noncommProd_equiv (Equiv.mulLeft a) (fun b => ρ b x) hc))

end

end OAI.NumberTheory.Quaternion.Arithmetic.CommutingOrbitNorm
