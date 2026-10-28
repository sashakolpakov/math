import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartRelations

/-! # Generation Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationCoordinates

noncomputable section

/-! On a normalized affine chart, the generation open detects equality of the actual classified relation modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} (R : CommRingCat.{u}) (f : Spec R ⟶ S)

theorem grassmannParameterAffine_chart_kernel_coefficients
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) (a : ι → ν)
    (v : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N) :
    (Matrix.toLin' ((HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v).map (Scheme.ΓSpecIso R).hom.hom)).ker = N.toSubmodule := by
  rw [← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange (Scheme.ΓSpecIso R).hom.hom a (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v)
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S v), ChartRelations.grassmannParameterAffine_chart_kernel R f N a v hv,
      ← HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp]
  have he : (Scheme.ΓSpecIso R).hom.hom.comp (Scheme.ΓSpecIso R).inv.hom = RingHom.id R := by
    ext x
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id x
  rw [he, HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id]

theorem grassmannChartGenerationOpen_affine_iff
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (K : Module.Grassmannian R (μ → R) (Fintype.card κ))
    (a : ι → ν) (b : κ → μ) (v : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)
    (w : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (hw : w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (F : α → Matrix μ ν R) (hF : ∀ t, N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' (F t))) :
    Grassmann.GenerationCharts.grassmannChartGenerationOpen a b v (fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom) = ⊤ ↔
      K.toSubmodule = ⨆ t, N.toSubmodule.map (Matrix.toLin' (F t)) := by
  let Q : Matrix ι ν Γ(Spec R, ⊤) := HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v
  let L : Matrix κ μ Γ(Spec R, ⊤) := HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S w
  have hQ : (Matrix.toLin' (Q.map (Scheme.ΓSpecIso R).hom.hom)).ker = N.toSubmodule :=
    grassmannParameterAffine_chart_kernel_coefficients R f N a v hv
  have hL : (Matrix.toLin' (L.map (Scheme.ΓSpecIso R).hom.hom)).ker = K.toSubmodule :=
    grassmannParameterAffine_chart_kernel_coefficients R f K b w hw
  have hround : (fun t => ((F t).map (Scheme.ΓSpecIso R).inv.hom).map (Scheme.ΓSpecIso R).hom.hom) = F := by
    funext t
    ext i j
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).inv_hom_id (F t i j)
  change HilbertConstruction.Matrix.SurjectivityOpen.matrixSurjectiveOpen (HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix a b Q
    (fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom)) = ⊤ ↔ _
  rw [HilbertConstruction.Matrix.SurjectivityOpen.matrixSurjectiveOpen_affine, Normalized.GenerationOpen.normalizedGenerationMatrix_map, hround]
  have hi : ∀ t, (Matrix.toLin' (Q.map (Scheme.ΓSpecIso R).hom.hom)).ker ≤
      ((Matrix.toLin' (L.map (Scheme.ΓSpecIso R).hom.hom)).ker).comap (Matrix.toLin' (F t)) := by
    rw [hQ, hL]
    exact hF
  have h := Normalized.GenerationCriterion.normalizedGenerationMatrix_surjective_iff a b _ _
    ((HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S v).map (Scheme.ΓSpecIso R).hom.hom)
    ((HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b S w).map (Scheme.ΓSpecIso R).hom.hom) F hi
  rw [hQ, hL] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationCoordinates
