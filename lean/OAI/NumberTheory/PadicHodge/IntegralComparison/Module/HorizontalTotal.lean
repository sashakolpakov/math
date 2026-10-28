import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Horizontal Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.HorizontalTotal.Comparison

noncomputable section

/-! Exact augmented rows compare with their genuine total complex for arbitrary
coefficient and module universes. -/

open _root_.CategoryTheory Limits

universe z t

variable (R : Type t) [CommRing R]

local instance moduleFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{z} R) :=
  Abelian.hasFiniteBiproducts

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun I => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete I)

local instance forgetColimits : PreservesColimitsOfSize.{z, z}
    (forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{z, t, z, z} R

variable (K : HomologicalComplex₂ (ModuleCat.{z} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  (A : CochainComplex (ModuleCat.{z} R) ℕ)
  (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
  (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
  (hmono : ∀ q, Mono (e q))
  (hrows : ∀ q n, (K.X q).ExactAt (n + 1))

include haug hmono hrows in
theorem quasiIso : QuasiIso ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) := by
  constructor
  intro n
  cases n with
  | zero =>
      exact AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero K A e he w (haug 0) hmono
  | succ n =>
      let G := forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}
      apply (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology _ G (n + 1)).mp
      let M := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K
      have haug' (q : ℕ) :
          (ShortComplex.mk (G.map (e q)) ((M.X q).d 0 1)
            (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w q)).Exact :=
        (haug q).map G
      have hmono' (q : ℕ) : Mono (G.map (e q)) := by
        have : Mono (e q) := hmono q
        infer_instance
      have hrows' : AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact M := by
        intro q m
        have h : (ShortComplex.mk ((K.X q).d m (m + 1)) ((K.X q).d (m + 1) (m + 2))
            ((K.X q).d_comp_d m (m + 1) (m + 2))).Exact :=
          ((K.X q).exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)).mp (hrows q m)
        exact h.map G
      have : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w) (n + 1) :=
        AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt M ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj A)
          (fun q => G.map (e q)) (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm G K A e he)
          (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w) haug' hmono' hrows' n
      have : IsIso (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison G K) :=
        (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G K).isIso_hom
      have h : QuasiIsoAt (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w ≫
          AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison G K) (n + 1) := inferInstance
      rw [AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
      exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.HorizontalTotal.Comparison
