import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFamilyDifferential
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.TangentComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AbelianConormalCharts

/-! # Lie Chart Conormal -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieChartConormal

noncomputable section

/-! The original geometric fiber Lie space is the dual of the
actual affine chart conormal, compatibly with each specified action generator. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {R I : Type} [CommRing R] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (a : I → R)
  (C : Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (a i)).left))
  {k : Type} [Field k] (q : Spec (.of k) ⟶ C.V.toScheme)

def chartConormalEquiv :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
    LiePoints.AlgebraicLie.Space (A.pullback (q ≫ C.V.ι)).scheme ≃ₗ[k]
      ((RingHom.ker C.targetSection.appTop.hom).Cotangent →ₗ[Γ(C.V.toScheme, ⊤)] k) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
  exact ((LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv A (q ≫ C.V.ι)).trans (C.targetTangentEquiv q).symm).trans
    (Affine.SectionLie.AffineSectionLie.conormalEquiv C.targetProjection C.targetSection
      (C.target_retraction (AbelianConormalCharts.abelian_unit_section A)) q)

theorem chartConormalEquiv_intertwines (i : I) (v : LiePoints.AlgebraicLie.Space (A.pullback (q ≫ C.V.ι)).scheme) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
    chartConormalEquiv A ρ a C q (LieAlgebraic.AlgebraicLie.map ((ρ.pullback (q ≫ C.V.ι)).map (a i)) v) =
      (chartConormalEquiv A ρ a C q v).comp
        (C.conormalOperator (AbelianConormalCharts.abelian_unit_section A) (AbelianConormalCharts.action_over A ρ a) (AbelianConormalCharts.action_unit_section A ρ a) i) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
  let eF := LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv A (q ≫ C.V.ι)
  let eC := C.targetTangentEquiv q
  have hmap : eC.symm (eF (LieAlgebraic.AlgebraicLie.map ((ρ.pullback (q ≫ C.V.ι)).map (a i)) v)) =
      C.tangentOperator q (AbelianConormalCharts.action_over A ρ a) (AbelianConormalCharts.action_unit_section A ρ a) i (eC.symm (eF v)) := by
    apply eC.injective
    rw [eC.apply_symm_apply]
    have h := C.targetTangentEquiv_operator q (AbelianConormalCharts.action_over A ρ a) (AbelianConormalCharts.action_unit_section A ρ a) i (eC.symm (eF v))
    change eC (C.tangentOperator q (AbelianConormalCharts.action_over A ρ a) (AbelianConormalCharts.action_unit_section A ρ a) i (eC.symm (eF v))) =
      LieFamilyDifferential.AlgebraicLie.familyDifferential A (q ≫ C.V.ι) ρ (a i) (eC (eC.symm (eF v))) at h
    rw [eC.apply_symm_apply] at h
    exact (LieFamilyDifferential.AlgebraicLie.fiberRelativeEquiv_map A (q ≫ C.V.ι) ρ (a i) v).trans h.symm
  exact (congrArg
    (Affine.SectionLie.AffineSectionLie.conormalEquiv C.targetProjection C.targetSection
      (C.target_retraction (AbelianConormalCharts.abelian_unit_section A)) q) hmap).trans
    (C.tangentOperator_conormal q (AbelianConormalCharts.abelian_unit_section A) (AbelianConormalCharts.action_over A ρ a)
      (AbelianConormalCharts.action_unit_section A ρ a) i (eC.symm (eF v)))

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieChartConormal
