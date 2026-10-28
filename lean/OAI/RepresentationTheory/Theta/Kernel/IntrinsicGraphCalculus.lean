import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus

/-! # Intrinsic Graph Calculus -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic

noncomputable section

/-! Matrix graph charts in the position-first convention used by the
native AdelicTheta comparison. -/

open scoped Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

variable {I : Type} [Fintype I] [DecidableEq I]

def positionBlock (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  P.submatrix Sum.inl Sum.inl + P.submatrix Sum.inl Sum.inr * Z

def momentumBlock (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  P.submatrix Sum.inr Sum.inl + P.submatrix Sum.inr Sum.inr * Z

def graphChart (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  momentumBlock P Z * (positionBlock P Z)⁻¹

omit [DecidableEq I] in
theorem positionBlock_apply (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ) (x : I → ℂ) (i : I) :
    (positionBlock P Z).mulVec x i = P.mulVec (Sum.elim x (Z.mulVec x)) (.inl i) := by
  rw [positionBlock,Matrix.add_mulVec,← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.submatrix_apply,
    Sum.elim_inl,Sum.elim_inr,Pi.add_apply]

omit [DecidableEq I] in
theorem momentumBlock_apply (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ) (x : I → ℂ) (i : I) :
    (momentumBlock P Z).mulVec x i = P.mulVec (Sum.elim x (Z.mulVec x)) (.inr i) := by
  rw [momentumBlock,Matrix.add_mulVec,← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.submatrix_apply,
    Sum.elim_inl,Sum.elim_inr,Pi.add_apply]

theorem blocks_of_fixed_graph (P : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ)
    (h : ∀ x : I → ℂ, P.mulVec (Sum.elim x (Z.mulVec x)) = Sum.elim x (Z.mulVec x)) :
    positionBlock P Z = 1 ∧ momentumBlock P Z = Z := by
  constructor
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    funext i
    change (positionBlock P Z).mulVec x i = (1 : Matrix I I ℂ).mulVec x i
    rw [positionBlock_apply,h,Matrix.one_mulVec]
    rfl
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    funext i
    change (momentumBlock P Z).mulVec x i = Z.mulVec x i
    rw [momentumBlock_apply,h]
    rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V}

omit [DecidableEq I] in
theorem submatrix_holomorphic (P : V → Matrix (I ⊕ I) (I ⊕ I) ℂ)
    (hP : DifferentiableOn ℂ P s) (a b : I → I ⊕ I) :
    DifferentiableOn ℂ (fun q => (P q).submatrix a b) s := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  exact (differentiable_apply (b j)).comp_differentiableOn
    ((differentiable_apply (a i)).comp_differentiableOn hP)

omit [DecidableEq I] in
theorem blocks_holomorphic (P : V → Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : V → Matrix I I ℂ)
    (hP : DifferentiableOn ℂ P s) (hZ : DifferentiableOn ℂ Z s) :
    DifferentiableOn ℂ (fun q => positionBlock (P q) (Z q)) s ∧
      DifferentiableOn ℂ (fun q => momentumBlock (P q) (Z q)) s := by
  constructor
  · exact (submatrix_holomorphic P hP Sum.inl Sum.inl).add
      (AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_product_holomorphic _ _
        (submatrix_holomorphic P hP Sum.inl Sum.inr) hZ)
  · exact (submatrix_holomorphic P hP Sum.inr Sum.inl).add
      (AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_product_holomorphic _ _
        (submatrix_holomorphic P hP Sum.inr Sum.inr) hZ)

theorem graphChart_holomorphic (P : V → Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : V → Matrix I I ℂ)
    (hP : DifferentiableOn ℂ P s) (hZ : DifferentiableOn ℂ Z s)
    (hdet : ∀ q ∈ s, (positionBlock (P q) (Z q)).det ≠ 0) :
    DifferentiableOn ℂ (fun q => graphChart (P q) (Z q)) s := by
  obtain ⟨hp,hq⟩ := blocks_holomorphic P Z hP hZ
  exact AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_product_holomorphic _ _ hq
    (AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_inverse_holomorphic _ hp hdet)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic
