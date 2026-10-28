import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.SectionProjections

/-! # Product Segre Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ProductSegreMap

noncomputable section

/-! On normalized charts the actual Segre morphism on a projective product
is the standard projective morphism with tensor-product coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} {T : Scheme.{u}} [Algebra R Γ(T, ⊤)]
variable (p : Segre.ChartProjections.SegreProjectiveIndex.{u} n m)
variable (r : Fin (n + 1) → Γ(T, ⊤)) (c : Fin (m + 1) → Γ(T, ⊤))
variable (hr : r p.1.down = 1) (hc : c p.2.down = 1)

def normalizedProjectiveProductMap :
    T ⟶ pullback (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom :=
  pullback.lift (ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) r p.1.down hr)
    (ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) c p.2.down hc)
    ((ProjectiveChart.Evaluation.projectiveChartMap_over (algebraMap R Γ(T, ⊤)) r p.1.down hr).trans
      (ProjectiveChart.Evaluation.projectiveChartMap_over (algebraMap R Γ(T, ⊤)) c p.2.down hc).symm)

theorem normalizedSegreSectionMap_product :
    Segre.SectionProjections.normalizedSegreSectionMap R p r c hr hc ≫ Segre.ProductComparison.segreToProduct (CommRingCat.of R) n m =
      normalizedProjectiveProductMap R p r c hr hc := by
  apply pullback.hom_ext
  · rw [Category.assoc, Segre.ProductComparison.segreToProduct_fst, Segre.SectionProjections.normalizedSegreSectionMap_row]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Segre.ProductComparison.segreToProduct_snd, Segre.SectionProjections.normalizedSegreSectionMap_column]
    exact (pullback.lift_snd _ _ _).symm

variable {d : ℕ} (e : Segre.ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1))

theorem normalizedProjectiveProductMap_segreStandard (i : Fin (d + 1))
    (hr : r (e.symm i).1.down = 1) (hc : c (e.symm i).2.down = 1) :
    (normalizedProjectiveProductMap R (e.symm i) r c hr hc ≫
      Segre.ProjectiveIsomorphism.affineSegreEmbedding (CommRingCat.of R) n m) ≫ (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left =
    ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) (ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c) i
      (Segre.StandardChartEvaluation.reindexedSegreSectionCoordinates_pivot_inverse e i r c hr hc) := by
  let q := normalizedProjectiveProductMap R (e.symm i) r c hr hc
  let z := Segre.SectionProjections.normalizedSegreSectionMap R (e.symm i) r c hr hc
  let s := Segre.ProjectiveIsomorphism.segreProductSchemeIso (CommRingCat.of R) n m
  let j := Segre.ProjectiveScheme.segreProjectiveInclusion (CommRingCat.of R)
    (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1)))
  let k := (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left
  have h : z ≫ s.hom = q := normalizedSegreSectionMap_product R (e.symm i) r c hr hc
  have hq : q ≫ s.inv = z := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (q ≫ (s.inv ≫ j)) ≫ k = _
  calc
    _ = (q ≫ s.inv) ≫ (j ≫ k) := by simp only [Category.assoc]
    _ = z ≫ (j ≫ k) := congrArg (fun a => a ≫ (j ≫ k)) hq
    _ = _ := Segre.StandardChartEvaluation.segreStandardChart_evaluation R e i r c hr hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ProductSegreMap
