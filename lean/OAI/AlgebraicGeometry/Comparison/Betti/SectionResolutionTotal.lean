import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Section Resolution Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SectionResolutionTotal

noncomputable section

/-! Exact augmented rows compare actual section complexes with their total resolutions in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

theorem additiveHorizontalEdge_quasiIso
    (B : HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ))
    (K : CochainComplex AddCommGrpCat.{0} ℕ) (e : ∀ q, K.X q ⟶ (B.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) :
    QuasiIso ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) := by
  constructor
  intro n
  cases n with
  | zero => exact TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he w (haug 0) hmono
  | succ n =>
      apply SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt B K e he w haug hmono ?_ n
      intro q p
      exact ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp (hrows q p)

theorem moduleHorizontalEdge_quasiIso {R : Type} [Ring R]
    (B : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ))
    (K : CochainComplex (ModuleCat.{0} R) ℕ) (e : ∀ q, K.X q ⟶ (B.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) :
    QuasiIso ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) := by
  let F := forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}
  have ha (q : ℕ) : (ShortComplex.mk (F.map (e q)) (((TotalComplexFunctor.mapBicomplex F B).X q).d 0 1)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact := (haug q).map F
  have hm (q : ℕ) : Mono (F.map (e q)) := by
    have := hmono q
    exact F.map_mono (e q)
  have hr (q p : ℕ) : ((TotalComplexFunctor.mapBicomplex F B).X q).ExactAt (p + 1) := by
    have h := ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp (hrows q p)
    exact (((TotalComplexFunctor.mapBicomplex F B).X q).exactAt_iff'
      p (p + 1) (p + 2) (by simp) (by simp)).mpr (h.map F)
  have hEdge : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w) :=
    additiveHorizontalEdge_quasiIso (TotalComplexFunctor.mapBicomplex F B) ((F.mapHomologicalComplex (.up ℕ)).obj K)
      (fun q => F.map (e q)) (TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) ha hm hr
  have hIso : IsIso (TotalComplexFunctor.totalComparison F B) := (TotalAdditiveFunctor.totalComparisonIsoOfAdditive F B).isIso_hom
  have h : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫ TotalComplexFunctor.totalComparison F B) := inferInstance
  rw [TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).mp h

end

end OAI.AlgebraicGeometry.Comparison.Betti.SectionResolutionTotal
