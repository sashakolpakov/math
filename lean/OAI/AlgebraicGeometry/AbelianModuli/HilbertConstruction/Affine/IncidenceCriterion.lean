import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.IncidenceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IncidenceNormalizedCriterion

/-! # Incidence Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceCriterion

noncomputable section

/-!
On an affine test with normalized chart lifts, the constructed incidence
condition is precisely containment of the actual classified relation modules.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

theorem grassmannIncidenceCondition_affine_chart (R : CommRingCat.{u}) (f : Spec R ⟶ S)
    (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (K : Module.Grassmannian R (μ → R) (Fintype.card κ))
    (hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (hK : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (a : ι → ν) (b : κ → μ)
    (v : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (w : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = x ≫ q)
    (hw : w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = x ≫ k)
    (F₀ : Matrix μ ν R)
    (hF : F.map x.left.appTop.hom = F₀.map (Scheme.ΓSpecIso R).inv.hom) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F x ↔
      N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F₀) := by
  rw [IncidenceNormalizedCriterion.grassmannIncidenceCondition_normalized q k F x a b v w hv hw,
    ChartRelations.grassmannParameterAffine_chart_kernel R f N a v (hv.trans hN),
    ChartRelations.grassmannParameterAffine_chart_kernel R f K b w (hw.trans hK), hF]
  exact Coordinate.IncidenceBaseChange.coordinateSubmoduleExtension_incidence_iff
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv N.toSubmodule K.toSubmodule F₀

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceCriterion
