import OAI.NumberTheory.PadicHodge.IntegralComparison.MultivariateTailIdentity

/-! # Degree Product Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeProductCoordinates

noncomputable section

/-! Polynomial coordinates for multiplying two independently shifted
finite families. The two distinguished variables are the shifts. -/

variable {ι κ : Type*}

def leftIndex : Option ι → Option (Option (ι ⊕ κ))
  | none => some none
  | some i => some (some (.inl i))

def rightIndex : Option κ → Option (Option (ι ⊕ κ))
  | none => none
  | some j => some (some (.inr j))

def leftSub (P : MvPolynomial (Option ι) ℚ) : MvPolynomial (Option (Option (ι ⊕ κ))) ℚ :=
  MvPolynomial.rename leftIndex P

def rightSub (P : MvPolynomial (Option κ) ℚ) : MvPolynomial (Option (Option (ι ⊕ κ))) ℚ :=
  MvPolynomial.rename rightIndex P

def productSub (P : MvPolynomial (Option ι × Option κ) ℚ) :
    MvPolynomial (Option (Option (ι ⊕ κ))) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun t => MvPolynomial.X (leftIndex t.1) * MvPolynomial.X (rightIndex t.2)) P

theorem eval_leftSub (v : Option (Option (ι ⊕ κ)) → ℚ) (P : MvPolynomial (Option ι) ℚ) :
    MvPolynomial.eval v (leftSub P) = MvPolynomial.eval (fun i => v (leftIndex i)) P :=
  MvPolynomial.eval_rename _ _ _

theorem eval_rightSub (v : Option (Option (ι ⊕ κ)) → ℚ) (P : MvPolynomial (Option κ) ℚ) :
    MvPolynomial.eval v (rightSub P) = MvPolynomial.eval (fun i => v (rightIndex i)) P :=
  MvPolynomial.eval_rename _ _ _

theorem eval_productSub (v : Option (Option (ι ⊕ κ)) → ℚ)
    (P : MvPolynomial (Option ι × Option κ) ℚ) :
    MvPolynomial.eval v (productSub P) =
      MvPolynomial.eval (fun t => v (leftIndex t.1) * v (rightIndex t.2)) P := by
  change MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [← MvPolynomial.eval_assoc]
  congr 2
  funext t
  simp only [Function.comp_apply, map_mul, MvPolynomial.eval_X]

theorem leftIndex_point (a : ι ⊕ κ → ℕ) (n m : ℕ) (i : Option ι) :
    Option.elim (leftIndex i) m (fun j => Option.elim j n a) =
      Option.elim i n (fun j => a (.inl j)) := by
  cases i <;> rfl

theorem rightIndex_point (a : ι ⊕ κ → ℕ) (n m : ℕ) (i : Option κ) :
    Option.elim (rightIndex i) m (fun j => Option.elim j n a) =
      Option.elim i m (fun j => a (.inr j)) := by
  cases i <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeProductCoordinates
