import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Column Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ColumnCokernel.Grassmannian

noncomputable section

/-! A column matrix with identity on selected rows has an explicit free cokernel on the complementary coordinates. -/

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {ν : Type w}
variable [Fintype ι] [DecidableEq ι]

def rowRestriction (b : ι → ν) : (ν → R) →ₗ[R] (ι → R) where
  toFun x := x ∘ b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def normalizedColumnProjection (b : ι → ν) (E : Matrix ν ι R) :
    (ν → R) →ₗ[R] ({j : ν // j ∉ Set.range b} → R) :=
  (LinearMap.pi (fun j => LinearMap.proj j.val)).comp
    (LinearMap.id - (Matrix.toLin' E).comp (rowRestriction b))

theorem rowRestriction_matrix (b : ι → ν) (E : Matrix ν ι R) (y : ι → R) :
    rowRestriction b (Matrix.toLin' E y) = Matrix.toLin' (E.submatrix b id) y := by
  funext i
  change Matrix.toLin' E y (b i) = Matrix.toLin' (E.submatrix b id) y i
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  rfl

theorem normalizedColumn_rows_section (b : ι → ν) (E : Matrix ν ι R)
    (hE : E.submatrix b id = 1) (y : ι → R) : rowRestriction b (Matrix.toLin' E y) = y := by
  rw [rowRestriction_matrix, hE, Matrix.toLin'_one, LinearMap.id_apply]

def complementaryCoordinatesExtend (b : ι → ν) (y : {j : ν // j ∉ Set.range b} → R) : ν → R := by
  classical
  exact fun j => if h : j ∈ Set.range b then 0 else y ⟨j, h⟩

omit [DecidableEq ι] in
theorem complementaryCoordinatesExtend_rows (b : ι → ν)
    (y : {j : ν // j ∉ Set.range b} → R) : rowRestriction b (complementaryCoordinatesExtend b y) = 0 := by
  classical
  funext i
  change complementaryCoordinatesExtend b y (b i) = 0
  simp [complementaryCoordinatesExtend]

theorem normalizedColumnProjection_surjective (b : ι → ν) (E : Matrix ν ι R) :
    Function.Surjective (normalizedColumnProjection b E) := by
  classical
  intro y
  refine ⟨complementaryCoordinatesExtend b y, ?_⟩
  funext j
  change complementaryCoordinatesExtend b y j.val -
    Matrix.toLin' E (rowRestriction b (complementaryCoordinatesExtend b y)) j.val = y j
  rw [complementaryCoordinatesExtend_rows, map_zero, Pi.zero_apply, sub_zero]
  simp only [complementaryCoordinatesExtend, dite_eq_right j.property]

theorem normalizedColumnProjection_kernel (b : ι → ν) (E : Matrix ν ι R)
    (hE : E.submatrix b id = 1) :
    (normalizedColumnProjection b E).ker = (Matrix.toLin' E).range := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨rowRestriction b x, ?_⟩
    funext j
    by_cases hj : j ∈ Set.range b
    · obtain ⟨i, rfl⟩ := hj
      exact congrFun (normalizedColumn_rows_section b E hE (rowRestriction b x)) i
    · have hjx := congrFun hx (⟨j, hj⟩ : {j : ν // j ∉ Set.range b})
      change x j - Matrix.toLin' E (rowRestriction b x) j = 0 at hjx
      exact (sub_eq_zero.mp hjx).symm
  · rintro ⟨y, rfl⟩
    change normalizedColumnProjection b E (Matrix.toLin' E y) = 0
    funext j
    change Matrix.toLin' E y j.val - Matrix.toLin' E (rowRestriction b (Matrix.toLin' E y)) j.val = 0
    rw [normalizedColumn_rows_section b E hE, sub_self]

def normalizedColumnCokernelEquiv (b : ι → ν) (E : Matrix ν ι R)
    (hE : E.submatrix b id = 1) :
    ((ν → R) ⧸ (Matrix.toLin' E).range) ≃ₗ[R] ({j : ν // j ∉ Set.range b} → R) :=
  (Submodule.quotEquivOfEq _ _ (normalizedColumnProjection_kernel b E hE).symm).trans
    ((normalizedColumnProjection b E).quotKerEquivOfSurjective (normalizedColumnProjection_surjective b E))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ColumnCokernel.Grassmannian
