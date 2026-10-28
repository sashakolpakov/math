import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductChartCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductProjections

/-! # Product Chart Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartScheme

noncomputable section

/-! Actual scheme isomorphisms from Segre charts to affine charts of the projective product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ} (p : ChartProjections.SegreProjectiveIndex.{u} n m)

def segreProductChartSchemeIso :
    (ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left ≅ Projective.ProductChartCover.projectiveProductChart R p :=
  Scheme.Spec.mapIso (ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down) (ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down)).symm

theorem segreProductChartSchemeIso_fst :
    (segreProductChartSchemeIso R p).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (ChartProductAlgebra.segreRowChartAlgebra R p).toRingHom) := by
  exact (Affine.ProductProjections.affineProductComparison_fst R (ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down)
    (ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down) (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).toAlgHom).trans
      (congrArg (fun f : ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down →ₐ[R] ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 =>
        Spec.map (CommRingCat.ofHom f.toRingHom)) (ChartProductAlgebra.segreHomogeneousProductChartEquiv_left R p))

theorem segreProductChartSchemeIso_snd :
    (segreProductChartSchemeIso R p).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (ChartProductAlgebra.segreColumnChartAlgebra R p).toRingHom) := by
  exact (Affine.ProductProjections.affineProductComparison_snd R (ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down)
    (ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down) (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).toAlgHom).trans
      (congrArg (fun f : ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down →ₐ[R] ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 =>
        Spec.map (CommRingCat.ofHom f.toRingHom)) (ChartProductAlgebra.segreHomogeneousProductChartEquiv_right R p))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartScheme
