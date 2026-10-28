import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Endpoint Orders -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.EndpointOrders

noncomputable section

/-! Ordered finite variable sets with one coordinate adjoined at either endpoint. -/

def finSuccWithBotEquiv (n : ℕ) : Fin (n + 1) ≃ WithBot (Fin n) := finSuccEquiv n

theorem finSuccWithBotEquiv_zero (n : ℕ) : finSuccWithBotEquiv n 0 = ⊥ := finSuccEquiv_zero

theorem finSuccWithBotEquiv_succ (n : ℕ) (i : Fin n) : finSuccWithBotEquiv n i.succ = (i : WithBot (Fin n)) :=
  finSuccEquiv_succ i

def finSuccWithBotOrderIso (n : ℕ) : Fin (n + 1) ≃o WithBot (Fin n) where
  __ := finSuccWithBotEquiv n
  map_rel_iff' := by
    intro a b
    refine Fin.cases ?_ (fun i => ?_) a
    · rw [finSuccWithBotEquiv_zero]
      simp
    · refine Fin.cases ?_ (fun j => ?_) b
      · rw [finSuccWithBotEquiv_succ, finSuccWithBotEquiv_zero]
        simp
      · rw [finSuccWithBotEquiv_succ, finSuccWithBotEquiv_succ, WithBot.coe_le_coe, Fin.succ_le_succ_iff]

def finSuccWithTopEquiv (n : ℕ) : Fin (n + 1) ≃ WithTop (Fin n) := finSuccEquivLast

theorem finSuccWithTopEquiv_last (n : ℕ) : finSuccWithTopEquiv n (Fin.last n) = ⊤ := finSuccEquivLast_last

theorem finSuccWithTopEquiv_castSucc (n : ℕ) (i : Fin n) :
    finSuccWithTopEquiv n i.castSucc = (i : WithTop (Fin n)) := finSuccEquivLast_castSucc i

def finSuccWithTopOrderIso (n : ℕ) : Fin (n + 1) ≃o WithTop (Fin n) where
  __ := finSuccWithTopEquiv n
  map_rel_iff' := by
    intro a b
    refine Fin.lastCases ?_ (fun i => ?_) a
    · refine Fin.lastCases ?_ (fun j => ?_) b
      · rw [finSuccWithTopEquiv_last]
        simp
      · rw [finSuccWithTopEquiv_last, finSuccWithTopEquiv_castSucc]
        simp
    · refine Fin.lastCases ?_ (fun j => ?_) b
      · rw [finSuccWithTopEquiv_castSucc, finSuccWithTopEquiv_last]
        simp
        exact (Fin.castSucc_lt_last i).le
      · rw [finSuccWithTopEquiv_castSucc, finSuccWithTopEquiv_castSucc,
          WithTop.coe_le_coe, Fin.castSucc_le_castSucc_iff]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.EndpointOrders
