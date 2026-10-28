import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set

/-! # Ordered Cech Top Support -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport

noncomputable section

/-! The full-support top Čech cochain is a single copy of the coefficient ring. -/

open _root_.AlgebraicGeometry.Scheme.Modules
universe u v
variable (R : Type u) [CommRing R] {ι : Type v} [LinearOrder ι] [Fintype ι]

def orderedCechTopIndex (n : ℕ) (hn : Fintype.card ι = n + 1) : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n :=
  ⟨monoEquivOfFin ι hn, (monoEquivOfFin ι hn).strictMono⟩

theorem orderedCechTopIndex_surjective (n : ℕ) (hn : Fintype.card ι = n + 1)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n) : Function.Surjective a.val :=
  ((Fintype.bijective_iff_injective_and_card a.val).mpr
    ⟨a.property.injective, by simpa using hn.symm⟩).2

theorem orderedCechTopIndex_unique (n : ℕ) (hn : Fintype.card ι = n + 1)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n) : a = orderedCechTopIndex n hn := by
  apply Subtype.ext
  apply (a.property.range_inj_of_wellFoundedLT (orderedCechTopIndex n hn).property).mp
  rw [Set.range_eq_univ.mpr (orderedCechTopIndex_surjective n hn a),
    Set.range_eq_univ.mpr (orderedCechTopIndex_surjective n hn (orderedCechTopIndex n hn))]

def orderedCechFullSupportTopEquiv (n : ℕ) (hn : Fintype.card ι = n + 1) :
    OrderedCechSupportContraction.OrderedCechSupportCochain R (Set.univ : Set ι) n ≃ₗ[R] R where
  toFun s := s.val (orderedCechTopIndex n hn)
  invFun r := ⟨fun _ => r, fun a ha =>
    (ha (fun x _ => orderedCechTopIndex_surjective n hn a x)).elim⟩
  left_inv s := by
    apply Subtype.ext
    funext a
    change s.val (orderedCechTopIndex n hn) = s.val a
    rw [orderedCechTopIndex_unique n hn a]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport
