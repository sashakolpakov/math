import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection

/-! # Projection Kernel -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ProjectionKernel.Construction

noncomputable section

/-! The kernel of diagonal-block projection on filtered units is
characterized by strict weight raising after subtracting the identity. -/

open scoped Classical

theorem matrix_filtered_projection_sub_one
    {R ι α : Type*} [CommRing R] [DecidableEq ι] [LinearOrder α]
    (w : ι → α) (M : Matrix ι ι R)
    (hM : Matrix.BlockTriangular (α := OrderDual α) M w)
    (hp : BlockProjection.Construction.weightBlockProjection w M = 1) (i j : ι) (hij : w i ≤ w j) :
    (M - 1) i j = 0 := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hlt
    change M i j - (1 : Matrix ι ι R) i j = 0
    rw [hM (i := i) (j := j) hlt, Matrix.one_apply_ne hne, sub_self]
  · have he := congrArg (fun N : Matrix ι ι R => N i j) hp
    rw [BlockProjection.Construction.weightBlockProjection_apply, ite_eq_left heq] at he
    change M i j - (1 : Matrix ι ι R) i j = 0
    rw [he, sub_self]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ProjectionKernel.Construction
