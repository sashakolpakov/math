import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.AtlasMaps

/-! # Normalized Chart Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint.Grassmannian

noncomputable section

/-! A normalized matrix over an arbitrary affine test ring determines an
actual relative Grassmannian chart point over any base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι ν : Type u} [DecidableEq ι]
variable {R : Type u} [CommRing R] {S : Scheme.{u}}
variable (f : Spec (.of R) ⟶ S) (a : ι → ν) (Q : Matrix ι ν R) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q)

def affineNormalizedChartPoint : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S :=
  ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).inv
    ⟨Q.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom,
      hQ.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom⟩

theorem affineNormalizedChartPoint_matrix :
    Normalized.AtlasMaps.Grassmannian.chartMatrix a S (affineNormalizedChartPoint f a Q hQ) =
      Q.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  congrArg Subtype.val
    (((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).toEquiv.apply_symm_apply
      ⟨Q.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom,
        hQ.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint.Grassmannian
