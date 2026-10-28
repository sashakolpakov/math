import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechExactRows
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison

/-! # Cech Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechStalk

noncomputable section

/-! Positive-degree comparison of the actual sheaf Čech resolution on every stalk. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

include hU

theorem sheafCechResolutionEdge_stalk_quasiIsoAt_succ (x : X) (n : ℕ) :
    QuasiIsoAt (((TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapHomologicalComplex (.up ℕ)).map
        (CechAugmentation.sheafCechResolutionEdge U K)) (n + 1) := by
  let F := TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let B := CechAugmentation.sheafCechBicomplex U K
  let e := CechAugmentation.sheafCechComplexAugmentation U K
  let he := fun q q' (_ : (ComplexShape.up ℕ).Rel q q') =>
    CechAugmentation.sheafCechComplexAugmentation_comm U K q q'
  let w := CechAugmentation.sheafCechComplexAugmentation_comp_d U K
  let M := TotalComplexFunctor.mapBicomplex F B
  have haug (q : ℕ) :
      (ShortComplex.mk (F.map (e q)) ((M.X q).d 0 1)
        (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact :=
    (CechExactRows.sheafCechComplexAugmentation_exact U hU K q).map F
  have hmono (q : ℕ) : Mono (F.map (e q)) := by
    have : Mono (e q) := CechExactRows.sheafCechComplexAugmentation_mono U hU K q
    infer_instance
  have hrows : SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact M := by
    intro q p
    have h : (ShortComplex.mk ((B.X q).d p (p + 1)) ((B.X q).d (p + 1) (p + 2))
        ((B.X q).d_comp_d p (p + 1) (p + 2))).Exact :=
      ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp
        (CechExactRows.sheafCechBicomplex_row_exact U hU K q p)
    exact h.map F
  have : QuasiIsoAt (TotalComplexEdge.mappedHorizontalEdge F B K e he w) (n + 1) :=
    SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt M ((F.mapHomologicalComplex (.up ℕ)).obj K)
      (fun q => F.map (e q)) (TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) haug hmono hrows n
  have : IsIso (TotalComplexFunctor.totalComparison F B) := (TotalComplexFunctor.totalComparisonIso F B).isIso_hom
  have h : QuasiIsoAt (TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫
      TotalComplexFunctor.totalComparison F B) (n + 1) := inferInstance
  rw [TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechStalk
