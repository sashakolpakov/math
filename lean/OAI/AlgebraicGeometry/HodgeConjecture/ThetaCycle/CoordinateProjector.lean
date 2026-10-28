import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorParameters
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorCharts

/-! # Coordinate Projector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateProjector.CM

noncomputable section

section

/-! ThetaCycle: actual total projectors in the fixed symplectic coordinates. -/

open scoped Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

def matrixColumnProduct {I J L : Type*} [Fintype J]
    (M : Matrix I J ℂ) (N : Matrix J L ℂ) : Matrix I L ℂ :=
  fun i l => ∑ j, M i j * N j l

theorem matrix_column_product_mulVec {I J L : Type*} [Fintype J] [Fintype L]
    (M : Matrix I J ℂ) (N : Matrix J L ℂ) (x : L → ℂ) :
    matrixColumnProduct M N *ᵥ x = M *ᵥ (N *ᵥ x) :=
  (Matrix.mulVec_mulVec x M N).symm

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def coordinateProjector (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (P : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K) :
    Matrix (Sum (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places))
      (Sum (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places)) ℂ :=
  LinearMap.toMatrix' (((ComplexTransition.CM.totalComplexCoordinates K C).toLinearMap.comp P).comp
    (ComplexTransition.CM.totalComplexCoordinates K C).symm.toLinearMap)

theorem coordinate_projector_mulVec (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (P : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K)
    (x : Sum (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) → ℂ) :
    coordinateProjector K C P *ᵥ x =
      ComplexTransition.CM.totalComplexCoordinates K C (P ((ComplexTransition.CM.totalComplexCoordinates K C).symm x)) := by
  change Matrix.toLin' (LinearMap.toMatrix' _) x = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem coordinate_projector_graph_fixed
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (P : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places))
    (hP : ∀ x, P (TotalPeriodGraphs.CM.totalGraphInAmbient K C Z x) = TotalPeriodGraphs.CM.totalGraphInAmbient K C Z x) :
    matrixColumnProduct (coordinateProjector K C P) (Matrix.fromRows Z.matrix 1) = Matrix.fromRows Z.matrix 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change matrixColumnProduct (coordinateProjector K C P) (Matrix.fromRows Z.matrix 1) *ᵥ x =
    Matrix.fromRows Z.matrix 1 *ᵥ x
  rw [matrix_column_product_mulVec, Matrix.fromRows_mulVec, Matrix.one_mulVec,
    coordinate_projector_mulVec]
  change ComplexTransition.CM.totalComplexCoordinates K C (P (TotalPeriodGraphs.CM.totalGraphInAmbient K C Z x)) = _
  rw [hP, TotalPeriodGraphs.CM.total_graph_coordinates]

theorem coordinate_projector_graph_image
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (P : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K)
    (Z₀ : Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places))
    (hP : ∀ w, ∃ x, P w = TotalPeriodGraphs.CM.totalGraphInAmbient K C Z x) :
    ProjectorCharts.CM.graphTop (coordinateProjector K C P) Z₀ = Z.matrix * ProjectorCharts.CM.graphBottom (coordinateProjector K C P) Z₀ := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨u, hu⟩ := hP ((ComplexTransition.CM.totalComplexCoordinates K C).symm (Sum.elim (Z₀ *ᵥ x) x))
  have hv : coordinateProjector K C P *ᵥ Sum.elim (Z₀ *ᵥ x) x = Sum.elim (Z.matrix *ᵥ u) u := by
    rw [coordinate_projector_mulVec, hu, TotalPeriodGraphs.CM.total_graph_coordinates]
  have ht : ProjectorCharts.CM.graphTop (coordinateProjector K C P) Z₀ *ᵥ x = Z.matrix *ᵥ u := by
    funext i
    change (matrixColumnProduct (coordinateProjector K C P) (Matrix.fromRows Z₀ 1) *ᵥ x) (Sum.inl i) = _
    rw [matrix_column_product_mulVec, Matrix.fromRows_mulVec, Matrix.one_mulVec, hv]
    rfl
  have hb : ProjectorCharts.CM.graphBottom (coordinateProjector K C P) Z₀ *ᵥ x = u := by
    funext i
    change (matrixColumnProduct (coordinateProjector K C P) (Matrix.fromRows Z₀ 1) *ᵥ x) (Sum.inr i) = _
    rw [matrix_column_product_mulVec, Matrix.fromRows_mulVec, Matrix.one_mulVec, hv]
    rfl
  change ProjectorCharts.CM.graphTop (coordinateProjector K C P) Z₀ *ᵥ x =
    (Z.matrix * ProjectorCharts.CM.graphBottom (coordinateProjector K C P) Z₀) *ᵥ x
  rw [← Matrix.mulVec_mulVec, hb, ht]

theorem coordinate_projectors_tendsto
    {A : Type*} {l : Filter A} (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (P : A → ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K) (P₀ : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K)
    (hP : ∀ w, Tendsto (fun a => P a w) l (𝓝 (P₀ w))) :
    Tendsto (fun a => coordinateProjector K C (P a)) l (𝓝 (coordinateProjector K C P₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let w := (ComplexTransition.CM.totalComplexCoordinates K C).symm (Pi.single j 1)
  have hc := ((ComplexTransition.CM.totalComplexCoordinates K C).toContinuousLinearEquiv.continuous.tendsto (P₀ w)).comp (hP w)
  have he := ((continuous_apply i).tendsto _).comp hc
  exact he

end

/-! ThetaCycle: holomorphic calculus for the actual graph-projection charts. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V}

theorem matrix_column_product_holomorphic
    {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    (M : V → Matrix I J ℂ) (N : V → Matrix J L ℂ)
    (hM : DifferentiableOn ℂ M s) (hN : DifferentiableOn ℂ N s) :
    DifferentiableOn ℂ (fun z => matrixColumnProduct (M z) (N z)) s := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro l
  simp only [matrixColumnProduct]
  fun_prop

theorem graph_frame_holomorphic {I : Type*} [Fintype I] [DecidableEq I]
    (Z : V → Matrix I I ℂ) (hZ : DifferentiableOn ℂ Z s) :
    DifferentiableOn ℂ (fun z => Matrix.fromRows (Z z) (1 : Matrix I I ℂ)) s := by
  apply differentiableOn_pi.mpr
  intro i
  cases i with
  | inl i =>
    change DifferentiableOn ℂ (fun z => Z z i) s
    exact (differentiable_apply i).comp_differentiableOn hZ
  | inr i =>
    change DifferentiableOn ℂ (fun _ : V => (1 : Matrix I I ℂ) i) s
    exact differentiableOn_const _

theorem graph_blocks_holomorphic {I : Type*} [Fintype I] [DecidableEq I]
    (P : V → Matrix (Sum I I) (Sum I I) ℂ) (Z : V → Matrix I I ℂ)
    (hP : DifferentiableOn ℂ P s) (hZ : DifferentiableOn ℂ Z s) :
    DifferentiableOn ℂ (fun z => ProjectorCharts.CM.graphTop (P z) (Z z)) s ∧
      DifferentiableOn ℂ (fun z => ProjectorCharts.CM.graphBottom (P z) (Z z)) s := by
  have h := matrix_column_product_holomorphic P (fun z => Matrix.fromRows (Z z) 1)
    hP (graph_frame_holomorphic Z hZ)
  constructor
  · apply differentiableOn_pi.mpr
    intro i
    exact (differentiable_apply (Sum.inl i)).comp_differentiableOn h
  · apply differentiableOn_pi.mpr
    intro i
    exact (differentiable_apply (Sum.inr i)).comp_differentiableOn h

theorem projector_graph_chart_holomorphic {I : Type*} [Fintype I] [DecidableEq I]
    (P : V → Matrix (Sum I I) (Sum I I) ℂ) (Z : V → Matrix I I ℂ)
    (hP : DifferentiableOn ℂ P s) (hZ : DifferentiableOn ℂ Z s)
    (hdet : ∀ z ∈ s, (ProjectorCharts.CM.graphBottom (P z) (Z z)).det ≠ 0) :
    DifferentiableOn ℂ (fun z => ProjectorCharts.CM.projectorGraphChart (P z) (Z z)) s := by
  obtain ⟨ht, hb⟩ := graph_blocks_holomorphic P Z hP hZ
  exact MatrixCalculus.CM.matrix_product_holomorphic _ _ ht (MatrixCalculus.CM.matrix_inverse_holomorphic _ hb hdet)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateProjector.CM
