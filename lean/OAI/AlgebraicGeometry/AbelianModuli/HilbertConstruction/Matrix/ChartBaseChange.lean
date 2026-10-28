import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PolynomialCoordinates

/-! # Chart Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ChartBaseChange

noncomputable section

/-! Split quotient-chart kernels commute with arbitrary change of coefficient ring. -/

universe u v w t

/-- Taking the target-ring span of the image of a span only requires semilinearity,
not surjectivity of the scalar map. -/
theorem semilinear_span_image_span {R : Type u} {B : Type v} [Ring R] [Ring B]
    {U : Type w} {V : Type t} [AddCommGroup U] [AddCommGroup V] [Module R U] [Module B V]
    {φ : R →+* B} (f : U →ₛₗ[φ] V) (s : Set U) :
    Submodule.span B (f '' (Submodule.span R s : Set U)) = Submodule.span B (f '' s) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (Submodule.image_span_subset_span f s)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/-- Apply a ring homomorphism to the coordinates of a finite free module. -/
def chartVectorMap {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (φ : R →+* B) (n : ℕ) : (Fin n → R) →ₛₗ[φ] (Fin n → B) where
  toFun x i := φ (x i)
  map_add' x y := by ext i; exact φ.map_add (x i) (y i)
  map_smul' r x := by ext i; exact φ.map_mul r (x i)

/-- Coordinatewise scalar change on both summands of a quotient chart. -/
def chartPairMap {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (φ : R →+* B) (k l : ℕ) :
    ((Fin k → R) × (Fin l → R)) →ₛₗ[φ] ((Fin k → B) × (Fin l → B)) where
  toFun x := (chartVectorMap φ k x.1, chartVectorMap φ l x.2)
  map_add' x y := Prod.ext (map_add (chartVectorMap φ k) x.1 y.1)
    (map_add (chartVectorMap φ l) x.2 y.2)
  map_smul' r x := Prod.ext (map_smulₛₗ (chartVectorMap φ k) r x.1)
    (map_smulₛₗ (chartVectorMap φ l) r x.2)

/-- The submodule obtained by extending a matrix-chart kernel is exactly the kernel
of the matrix with its coefficients mapped to the new ring. -/
theorem matrixChart_kernel_baseChange {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (φ : R →+* B) {k l : ℕ} (M : Matrix (Fin k) (Fin l) R) :
    Submodule.span B (chartPairMap φ k l ''
      ((LinearMap.id.coprod M.mulVecLin).ker : Set ((Fin k → R) × (Fin l → R)))) =
      (LinearMap.id.coprod (M.map φ).mulVecLin).ker := by
  let bR := Pi.basisFun R (Fin l)
  let bB := Pi.basisFun B (Fin l)
  have hgen (j : Fin l) : chartPairMap φ k l (-M.mulVecLin (bR j), bR j) =
      (-(M.map φ).mulVecLin (bB j), bB j) := by
    ext i <;> simp [chartPairMap, chartVectorMap, bR, bB, Pi.basisFun_apply,
      Pi.single_apply, apply_ite]
    split_ifs <;> simp_all
  rw [Quotient.ChartKernels.quotientChart_kernel_span bR, semilinear_span_image_span,
    Quotient.ChartKernels.quotientChart_kernel_span bB, ← Set.range_comp]
  exact congrArg (Submodule.span B) (congrArg Set.range (funext hgen))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ChartBaseChange
