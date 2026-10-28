import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Fibers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.TotalExists
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison

/-! # Sheaf Total Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.SheafTotalComparison.LargeSheafTotalComparison

noncomputable section

/-!
# Exact augmented rows compare with the total complex of native module sheaves

Exact conservative fibers reduce the comparison to the proved
first-quadrant calculation for abelian groups. Every degree is included.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  (K : HomologicalComplex₂ (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R))
    (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  (A : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) ℕ)
  (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
  (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
  (hmono : ∀ q, Mono (e q))
  (hrows : ∀ q n, (K.X q).ExactAt (n + 1))

include haug hmono hrows in
theorem quasiIso : QuasiIso ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) := by
  constructor
  intro n
  cases n with
  | zero =>
      exact Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero K A e he w (haug 0) hmono
  | succ n =>
      apply LargeZariski.Fibers.LargeZariskiFibers.quasiIsoAt_of_underlying R X
      intro x
      let G := LargeZariski.Fibers.LargeZariskiFibers.underlying R X x
      let M := Comparison.Betti.TotalComplexFunctor.mapBicomplex G K
      have haug' (q : ℕ) :
          (ShortComplex.mk (G.map (e q)) ((M.X q).d 0 1)
            (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w q)).Exact :=
        (haug q).map G
      have hmono' (q : ℕ) : Mono (G.map (e q)) := by
        have : Mono (e q) := hmono q
        infer_instance
      have hrows' : SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact M := by
        intro q m
        have h : (ShortComplex.mk ((K.X q).d m (m + 1)) ((K.X q).d (m + 1) (m + 2))
            ((K.X q).d_comp_d m (m + 1) (m + 2))).Exact :=
          ((K.X q).exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)).mp (hrows q m)
        exact h.map G
      have : QuasiIsoAt (Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w) (n + 1) :=
        SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt M ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj A)
          (fun q => G.map (e q)) (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm G K A e he)
          (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w) haug' hmono' hrows' n
      have : IsIso (Comparison.Betti.TotalComplexFunctor.totalComparison G K) :=
        (Comparison.Betti.TotalComplexFunctor.totalComparisonIso G K).isIso_hom
      have h : QuasiIsoAt (Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w ≫
          Comparison.Betti.TotalComplexFunctor.totalComparison G K) (n + 1) := inferInstance
      rw [Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
      exact h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.SheafTotalComparison.LargeSheafTotalComparison
