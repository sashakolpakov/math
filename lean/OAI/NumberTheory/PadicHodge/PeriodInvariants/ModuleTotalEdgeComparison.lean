import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalComparison
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.QuasiIso

/-! # Module Total Edge Comparison -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleTotalEdgeComparison

noncomputable section

/-! # The exact-row total-complex comparison retains module linearity -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

universe u
variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ))

def RowsExact : Prop := ∀ q p,
  (ShortComplex.mk ((K.X q).d p (p + 1)) ((K.X q).d (p + 1) (p + 2))
    ((K.X q).d_comp_d p (p + 1) (p + 2))).Exact

variable (A : CochainComplex (ModuleCat.{u} R) ℕ)
  (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
    e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
  (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
  (hmono : ∀ q, Mono (e q)) (hrows : RowsExact K)

include haug hmono hrows in
theorem horizontal (n : ℕ) : QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) (n + 1) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have hm : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge F K A e he w) (n + 1) :=
    AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)
      ((F.mapHomologicalComplex (.up ℕ)).obj A) (fun q => F.map (e q))
      (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm F K A e he)
      (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d F K A e w)
      (fun q => (haug q).map F)
      (fun q => by
        have : Mono (e q) := hmono q
        exact inferInstanceAs (Mono (F.map (e q))))
      (fun q p => (hrows q p).map F) n
  have hi : IsIso (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K) := by
    have (q : ℕ) : IsIso ((AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K).f q) :=
      AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparisonComponent_isIso_of_additive F K q
    exact HomologicalComplex.Hom.isIso_of_components _
  have hc : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge F K A e he w ≫
      AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K) (n + 1) := inferInstance
  rw [AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at hc
  exact (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) F (n + 1)).mp hc

variable (B : CochainComplex (ModuleCat.{u} R) ℕ)
  (v : ∀ p, B.X p ⟶ (K.X 0).X p)
  (hv : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
    v p ≫ (K.X 0).d p p' = B.d p p' ≫ v p')
  (wv : ∀ p, v p ≫ (K.d 0 1).f p = 0)
  (haugv : ∀ p, (ShortComplex.mk (v p) ((K.d 0 1).f p) (wv p)).Exact)
  (hmonov : ∀ p, Mono (v p)) (hcols : RowsExact K.flip)

include haugv hmonov hcols in
theorem vertical (n : ℕ) : QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge K) B v hv wv) (n + 1) := by
  have : QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K.flip) B v hv wv) (n + 1) :=
    horizontal K.flip B v hv wv haugv hmonov hcols n
  change QuasiIsoAt ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K.flip) B v hv wv ≫ (K.totalFlipIso (.up ℕ)).hom) (n + 1)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleTotalEdgeComparison
