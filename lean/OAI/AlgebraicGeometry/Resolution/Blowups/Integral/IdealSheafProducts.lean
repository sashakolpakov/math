import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Ideal Sheaf Products -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts.Construction

noncomputable section

/-! Products of nonzero native ideal sheaves on an integral scheme are nonzero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_mul_ne_bot {X : Scheme} [IsIntegral X]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ := by
  intro h
  let x : X := Nonempty.some inferInstance
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let W : X.affineOpens := ⟨U, hU⟩
  let : Nonempty W.1 := ⟨⟨x, hx⟩⟩
  have he : I.ideal W * J.ideal W = ⊥ := congrArg (fun K : X.IdealSheafData => K.ideal W) h
  exact (Ideal.mul_eq_bot.mp he).elim
    (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI W) (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen J hJ W)

theorem idealSheaf_top_ne_bot {X : Scheme} [Nonempty X] : (⊤ : X.IdealSheafData) ≠ ⊥ := by
  intro h
  let x : X := Nonempty.some inferInstance
  have hx : x ∈ (⊥ : X.IdealSheafData).support := by rw [Scheme.IdealSheafData.support_bot]; trivial
  rw [← h, Scheme.IdealSheafData.support_top] at hx
  exact hx

theorem idealSheaf_pow_ne_bot {X : Scheme} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (n : ℕ) : I ^ n ≠ ⊥ := by
  induction n with
  | zero =>
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
      exact idealSheaf_top_ne_bot
  | succ n ih => rw [pow_succ]; exact idealSheaf_mul_ne_bot _ _ ih hI

theorem idealSheaf_finset_prod_ne_bot {X : Scheme} [IsIntegral X] {ι : Type}
    (D : ι → X.IdealSheafData) (S : Finset ι) (hD : ∀ i ∈ S, D i ≠ ⊥) :
    (∏ i ∈ S, D i) ≠ ⊥ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
      exact idealSheaf_top_ne_bot
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact idealSheaf_mul_ne_bot _ _ (hD i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hD j (Finset.mem_insert_of_mem hj)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts.Construction
