import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedGrassmannian

/-! # Chart Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartRelations

noncomputable section

/-!
For an affine Grassmannian point, every normalized chart matrix has exactly
the coefficient-extended relation submodule of the classified quotient.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {S : Scheme.{u}}

omit [Fintype ν] [DecidableEq ν] in
theorem normalizedMatrixClassifyingMap_chart {T : Over S} (a : ι → ν)
    (v : T ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) :
    HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S v) =
      v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S := by
  exact congrArg (fun w => w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S)
    (((HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).toEquiv.symm_apply_apply v)

theorem grassmannParameterAffine_chart_kernel (R : CommRingCat.{u}) (f : Spec R ⟶ S)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) (a : ι → ν)
    (v : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N) :
    (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v)).ker =
      HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (Scheme.ΓSpecIso R).inv.hom N.toSubmodule := by
  let Q := HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v
  let Q₀ := Q.map (Scheme.ΓSpecIso R).hom.hom
  have hQ₀ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q₀ :=
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S v).map (Scheme.ΓSpecIso R).hom.hom
  have hround : Q₀.map (Scheme.ΓSpecIso R).inv.hom = Q := by
    ext i j
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id (Q i j)
  have hclass : Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q₀ hQ₀) =
      v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S := by
    have he : (⟨Q₀.map (Scheme.ΓSpecIso R).inv.hom,
        hQ₀.map (Scheme.ΓSpecIso R).inv.hom⟩ :
        {L : Matrix ι ν Γ((Over.mk f).left, ⊤) // HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a L}) =
          ⟨Q, HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S v⟩ := Subtype.ext hround
    exact (NormalizedGrassmannian.grassmannParameterAffinePointEquiv_normalized R a Q₀ hQ₀ f).trans
      ((congrArg (fun L : {L : Matrix ι ν Γ((Over.mk f).left, ⊤) // HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a L} =>
        HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap (T := Over.mk f) a L.val L.property) he).trans
          (normalizedMatrixClassifyingMap_chart a v))
  have hN : N = HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q₀ hQ₀ :=
    (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f).injective (hv.symm.trans hclass.symm)
  rw [hN]
  change (Matrix.toLin' Q).ker =
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (Scheme.ΓSpecIso R).inv.hom (Matrix.toLin' Q₀).ker
  rw [HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange _ a Q₀ hQ₀, hround]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartRelations
