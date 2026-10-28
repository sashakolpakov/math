import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.StalkQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero

/-! # Resolution Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ResolutionTotal

noncomputable section

/-! A nonnegative bicomplex resolving every term of a sheaf complex has its original augmentation as a total quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}}
  (B : HomologicalComplex₂ (TopCat.Sheaf AddCommGrpCat.{0} X) (.up ℕ) (.up ℕ))
  [B.HasTotal (.up ℕ)] (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
  (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)
  (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
  (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1))

include haug hmono hrows

theorem sheafHorizontalEdge_stalk_quasiIsoAt_succ (x : X) (n : ℕ) :
    QuasiIsoAt (((TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapHomologicalComplex (.up ℕ)).map
        ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w)) (n + 1) := by
  let F := TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let M := TotalComplexFunctor.mapBicomplex F B
  have haug' (q : ℕ) :
      (ShortComplex.mk (F.map (e q)) ((M.X q).d 0 1)
        (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact :=
    (haug q).map F
  have hmono' (q : ℕ) : Mono (F.map (e q)) := by
    have := hmono q
    infer_instance
  have hrows' : SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact M := by
    intro q p
    have h : (ShortComplex.mk ((B.X q).d p (p + 1)) ((B.X q).d (p + 1) (p + 2))
        ((B.X q).d_comp_d p (p + 1) (p + 2))).Exact :=
      ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp (hrows q p)
    exact h.map F
  have : QuasiIsoAt (TotalComplexEdge.mappedHorizontalEdge F B K e he w) (n + 1) :=
    SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt M ((F.mapHomologicalComplex (.up ℕ)).obj K)
      (fun q => F.map (e q)) (TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) haug' hmono' hrows' n
  have : IsIso (TotalComplexFunctor.totalComparison F B) := (TotalComplexFunctor.totalComparisonIso F B).isIso_hom
  have h : QuasiIsoAt (TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫ TotalComplexFunctor.totalComparison F B) (n + 1) := inferInstance
  rw [TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

theorem sheafHorizontalEdge_quasiIso : QuasiIso ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) := by
  constructor
  intro n
  cases n with
  | zero => exact TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he w (haug 0) hmono
  | succ n =>
    exact (StalkQuasiIso.Cech.sheafQuasiIsoAt_iff_stalk ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) (n + 1)).mpr
      (fun x => sheafHorizontalEdge_stalk_quasiIsoAt_succ B K e he w haug hmono hrows x n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ResolutionTotal
