import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.BoundarySections
import OAI.AlgebraicGeometry.Comparison.Betti.StalkClosedLiftCriterion
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafStalkQuasiIso

/-! # Comparison Zero -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.ComparisonZero.Hodge

noncomputable section

/-! The actual filtered holomorphic comparison is a quasi-isomorphism
in degree zero whenever that degree is retained. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicFilteredSheafMap_quasiIsoAt_zero (r : ℤ) (hr : r ≤ 0) :
    QuasiIsoAt (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) 0 := by
  apply Module.SheafStalkQuasiIso.Holomorphic.moduleSheafQuasiIsoAt_of_stalk (X := TopCat.of M)
    (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) 0
  intro x
  let G := sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Holomorphic.SheafComplex.sheafComplex E M) r)
  let L := (G.mapHomologicalComplex (.up ℕ)).obj (SmoothComplex.Hodge.filteredSmoothSheafComplex E M r)
  let f : K ⟶ L := (G.mapHomologicalComplex (.up ℕ)).map (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r)
  have hm (k : ℕ) (hk : r ≤ (k : ℤ)) : Mono (f.f k) := by
    have h := BoundarySections.Hodge.holomorphicFilteredSheafMap_f_mono E M r k hk
    change Mono (G.map ((Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r).f k))
    infer_instance
  let φ := (shortComplexFunctor' _ (.up ℕ) 0 0 1).map f
  have hφ2 : Mono φ.τ₂ := hm 0 hr
  have hφ3 : Mono φ.τ₃ := hm 1 (by omega)
  have hq := StalkClosedLiftCriterion.Homology.stalk_short_quasiIso_of_local_lift (X := TopCat.of M) φ x
    (K.shape 0 0 (by simp)) (L.shape 0 0 (by simp)) (fun U y hy => ?_)
  · change QuasiIsoAt (((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex
      (.up ℕ)).map f) 0
    rw [CochainComplex.quasiIsoAt₀_iff]
    exact hq
  · change ((SmoothComplex.Hodge.filteredSmoothSheafComplex E M r).d 0 1).hom.app (op U) y = 0 at hy
    rw [SmoothComplex.Hodge.filteredSmoothSheafComplex_d] at hy
    exact BoundarySections.Hodge.filtered_boundary_section_lift E M U r 0 hr (Or.inl rfl) y hy

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.ComparisonZero.Hodge
