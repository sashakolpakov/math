import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Immersion

/-! # Quasi Compact -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian

noncomputable section

/-! Finite matrices have finitely many pivot charts. Since each chart is affine
over the parameter scheme, their glued rank locus is quasi-compact over it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

instance matrixPivotAmbientOpenInclusion_isAffineHom (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsAffineHom (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotAmbientOpenInclusion M A p).left :=
  inferInstanceAs (IsAffineHom (M.left.basicOpen (A.submatrix p.2 p.1).det).ι)

instance matrixPivotChartInclusion_isAffineHom (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsAffineHom (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left := by
  rw [← MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen_inclusion]
  change IsAffineHom ((MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p).left ≫
    (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotAmbientOpenInclusion M A p).left)
  infer_instance

instance matrixRankStructureMap_quasiCompact [Finite μ] [Finite ν] :
    QuasiCompact (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  have heq : (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) ⁻¹' (U : Set M.left) =
      ⋃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν, (Data.Grassmannian.matrixRankChartMap M A p) ''
        ((MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left ⁻¹' (U : Set M.left)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, y, rfl⟩ := Data.Grassmannian.matrixRankCharts_cover M A x
      refine Set.mem_iUnion.mpr ⟨p, y, ?_, rfl⟩
      change (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left y ∈ U
      change Data.Grassmannian.matrixRankStructureMap M A (Data.Grassmannian.matrixRankChartMap M A p y) ∈ U at hx
      rwa [← Scheme.Hom.comp_apply, Data.Grassmannian.matrixRankChartMap_structureMap] at hx
    · intro hx
      obtain ⟨p, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      change Data.Grassmannian.matrixRankStructureMap M A (Data.Grassmannian.matrixRankChartMap M A p y) ∈ U
      rw [← Scheme.Hom.comp_apply, Data.Grassmannian.matrixRankChartMap_structureMap]
      exact hy
  change IsCompact ((Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) ⁻¹' (U : Set M.left))
  rw [heq]
  apply isCompact_iUnion
  intro p
  exact ((hU.preimage (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left).isCompact).image
    (Data.Grassmannian.matrixRankChartMap M A p).continuous

instance matrixRankParameterMap_quasiCompact [Finite μ] [Finite ν] :
    QuasiCompact (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A).left := matrixRankStructureMap_quasiCompact M A

/-- The full geometric and functorial conclusion for finite matrix flat-rank
loci, with the actual flatness/rank condition on arbitrary test schemes. -/
theorem matrix_flat_fixed_rank_immersion [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν] :
    ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧
      LocallyOfFiniteType j.left ∧ QuasiCompact j.left ∧
      ∃ e : yoneda.obj Z ≅ (Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ι) M A).toFunctor,
        e.hom ≫ (Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ι) M A).ι = yoneda.map j := by
  rw [Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor_eq]
  exact ⟨Data.Grassmannian.matrixRankOver (ι := ι) M A, Data.Grassmannian.matrixRankParameterMap M A, inferInstance,
    inferInstance, inferInstance, Representation.Grassmannian.matrixRankRepresentation M A, Representation.Grassmannian.matrixRankRepresentation_inclusion M A⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian
