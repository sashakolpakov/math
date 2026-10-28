import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison

/-! # Total Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge.TotalEdgeComparison

noncomputable section

/-! Exact augmented rows give a total-complex comparison after any exact additive realization in abelian groups. -/

open _root_.CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] [F.PreservesHomology]
  [PreservesColimitsOfSize.{0, 0} F]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  (K : CochainComplex C ℕ) (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)

theorem mapped_edge_quasiIsoAt_succ
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q))
    (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) (n : ℕ) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w)) (n + 1) := by
  let M := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F B
  have haug' (q : ℕ) :
      (ShortComplex.mk (F.map (e q)) ((M.X q).d 0 1)
        (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact := (haug q).map F
  have hmono' (q : ℕ) : Mono (F.map (e q)) := by
    have : Mono (e q) := hmono q
    infer_instance
  have hrows' : AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact M := by
    intro q p
    have h := ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp (hrows q p)
    exact h.map F
  have : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge F B K e he w) (n + 1) :=
    AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt M ((F.mapHomologicalComplex (.up ℕ)).obj K)
      (fun q => F.map (e q)) (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) haug' hmono' hrows' n
  have : IsIso (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F B) := (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonIso F B).isIso_hom
  have h : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫
      AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F B) (n + 1) := inferInstance
  rw [AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge.TotalEdgeComparison
