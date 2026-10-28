import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Chart

/-! # Incidence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Incidence

noncomputable section

/-!
Incidence conditions in Grassmannian coordinates. A linear map preserves
the two kernel submodules exactly when an explicit matrix expression
vanishes. Its entries are polynomial expressions in the chart coordinates.
-/

universe u v w v' w'

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {V' : Type v'} [AddCommGroup V'] [Module R V']
variable {W' : Type w'} [AddCommGroup W'] [Module R W']

def chartKernelGenerator (L : W →ₗ[R] V) : W →ₗ[R] V × W :=
  (-L).prod LinearMap.id

theorem chartKernelGenerator_range (L : W →ₗ[R] V) :
    (chartKernelGenerator L).range = CoordinateCharts.chartKernel L := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    change -L w + L w = 0
    exact neg_add_cancel _
  · intro hx
    change x.1 + L x.2 = 0 at hx
    refine ⟨x.2, Prod.ext ?_ rfl⟩
    exact (eq_neg_of_add_eq_zero_left hx).symm

theorem chart_incidence_iff (L : W →ₗ[R] V) (K : W' →ₗ[R] V')
    (F : V × W →ₗ[R] V' × W') :
    CoordinateCharts.chartKernel L ≤ (CoordinateCharts.chartKernel K).comap F ↔
      (CoordinateCharts.chartQuotientMap K).comp (F.comp (chartKernelGenerator L)) = 0 := by
  rw [← chartKernelGenerator_range L]
  change (chartKernelGenerator L).range ≤ ((CoordinateCharts.chartQuotientMap K).comp F).ker ↔ _
  rw [LinearMap.range_le_ker_iff, LinearMap.comp_assoc]

def blockLinearMap (A : V →ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') : V × W →ₗ[R] V' × W' :=
  (A.comp (LinearMap.fst R V W) + B.comp (LinearMap.snd R V W)).prod
    (C.comp (LinearMap.fst R V W) + D.comp (LinearMap.snd R V W))

theorem chart_incidence_blocks (L : W →ₗ[R] V) (K : W' →ₗ[R] V')
    (A : V →ₗ[R] V') (B : W →ₗ[R] V') (C : V →ₗ[R] W') (D : W →ₗ[R] W') :
    CoordinateCharts.chartKernel L ≤ (CoordinateCharts.chartKernel K).comap (blockLinearMap A B C D) ↔
      B - A.comp L + K.comp D - (K.comp C).comp L = 0 := by
  rw [chart_incidence_iff]
  have hcomp : (CoordinateCharts.chartQuotientMap K).comp
      ((blockLinearMap A B C D).comp (chartKernelGenerator L)) =
      B - A.comp L + K.comp D - (K.comp C).comp L := by
    ext w
    change A (-L w) + B w + K (C (-L w) + D w) =
      B w - A (L w) + K (D w) - K (C (L w))
    rw [map_neg, map_neg, map_add, map_neg]
    abel
  rw [hcomp]

variable {ι κ ι' κ' : Type v}
variable [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']

def incidenceMatrix (L : Matrix ι κ R) (K : Matrix ι' κ' R)
    (A : Matrix ι' ι R) (B : Matrix ι' κ R) (C : Matrix κ' ι R) (D : Matrix κ' κ R) :
    Matrix ι' κ R := B - A * L + K * D - K * C * L

omit [Fintype ι'] [DecidableEq ι'] in
theorem chart_incidence_matrix (L : Matrix ι κ R) (K : Matrix ι' κ' R)
    (A : Matrix ι' ι R) (B : Matrix ι' κ R) (C : Matrix κ' ι R) (D : Matrix κ' κ R) :
    CoordinateCharts.chartKernel (Matrix.toLin' L) ≤ (CoordinateCharts.chartKernel (Matrix.toLin' K)).comap
      (blockLinearMap (Matrix.toLin' A) (Matrix.toLin' B) (Matrix.toLin' C) (Matrix.toLin' D)) ↔
      incidenceMatrix L K A B C D = 0 := by
  rw [chart_incidence_blocks]
  have h : Matrix.toLin' (incidenceMatrix L K A B C D) =
      Matrix.toLin' B - (Matrix.toLin' A).comp (Matrix.toLin' L) +
        (Matrix.toLin' K).comp (Matrix.toLin' D) -
          ((Matrix.toLin' K).comp (Matrix.toLin' C)).comp (Matrix.toLin' L) := by
    simp only [incidenceMatrix, map_sub, map_add, Matrix.toLin'_mul]
  rw [← h]
  exact (Matrix.toLin'.map_eq_zero_iff)

omit [Fintype κ] [Fintype ι'] [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
theorem incidenceMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (L : Matrix ι κ R) (K : Matrix ι' κ' R)
    (A : Matrix ι' ι R) (B : Matrix ι' κ R) (C : Matrix κ' ι R) (D : Matrix κ' κ R) :
    (incidenceMatrix L K A B C D).map φ =
      incidenceMatrix (L.map φ) (K.map φ) (A.map φ) (B.map φ) (C.map φ) (D.map φ) := by
  simp only [incidenceMatrix, Matrix.map_sub _ φ.map_sub, Matrix.map_add _ φ.map_add,
    Matrix.map_mul]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Incidence
