import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyFiniteProducts

/-! # Nonempty Product Property -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyProductProperty

noncomputable section

/-! A property stable under isomorphism and adjoining one factor holds on every nonempty finite product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {ι : Type w}
  (F : ι → C) (Q : C → Prop)
  (hiso : ∀ {U V : C}, (U ≅ V) → Q U → Q V)
  (hbase : ∀ i, Q (F i)) (hstep : ∀ (U : C), Q U → ∀ i, Q (U ⨯ F i))

include hiso hbase hstep in
theorem product : ∀ (n : ℕ) (t : Fin (n + 1) → ι), Q (∏ᶜ (fun a => F (t a)))
  | 0, t => by
    let : Unique (Fin 1) :=
      { default := ⟨0, Nat.zero_lt_one⟩
        uniq i := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)) }
    exact hiso (limit.isoLimitCone (limitConeOfUnique (fun a => F (t a)))).symm (hbase (t 0))
  | n + 1, t => by
    let c₁ := limit.cone (Discrete.functor (fun a : Fin (n + 1) => F (t a.succ)))
    let c₂ := limit.cone (pair (F (t 0)) c₁.pt)
    have htail : Q c₁.pt := product n (fun a => t a.succ)
    have hpair : Q c₂.pt := hiso (prod.braiding c₁.pt (F (t 0))) (hstep c₁.pt htail (t 0))
    let hc : IsLimit (extendFan c₁ c₂) := extendFanIsLimit (fun a => F (t a)) (limit.isLimit _) (limit.isLimit _)
    let e : (∏ᶜ (fun a => F (t a))) ≅ c₂.pt :=
      (limit.isLimit (Discrete.functor (fun a => F (t a)))).conePointUniqueUpToIso hc
    exact hiso e.symm hpair

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyProductProperty
