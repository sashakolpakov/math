import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.ComparisonZero
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Below

/-! # Boundary -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Boundary.Hodge

noncomputable section

/-! The actual filtered comparison is a quasi-isomorphism in a positive
degree equal to the truncation index, using the constructed closed-section lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicFilteredSheafMap_quasiIsoAt_boundary (n : ℕ) :
    QuasiIsoAt (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M ((n + 1 : ℕ) : ℤ)) (n + 1) := by
  let r : ℤ := (n + 1 : ℕ)
  apply Module.SheafStalkQuasiIso.Holomorphic.moduleSheafQuasiIsoAt_of_stalk (X := TopCat.of M)
    (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) (n + 1)
  intro x
  let G := sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Holomorphic.SheafComplex.sheafComplex E M) r)
  let L := (G.mapHomologicalComplex (.up ℕ)).obj (SmoothComplex.Hodge.filteredSmoothSheafComplex E M r)
  let f : K ⟶ L := (G.mapHomologicalComplex (.up ℕ)).map (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r)
  have hm (k : ℕ) (hk : r ≤ (k : ℤ)) : Mono (f.f k) := by
    have h := BoundarySections.Hodge.holomorphicFilteredSheafMap_f_mono E M r k hk
    change Mono (G.map ((Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r).f k))
    infer_instance
  have hKS : K.d n (n + 1) = 0 := by
    have hz := Brutal.Complex.brutal_isZero_X_below (Holomorphic.SheafComplex.sheafComplex E M) r n (by
      dsimp [r]
      omega)
    have hd : (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Holomorphic.SheafComplex.sheafComplex E M) r).d n (n + 1) = 0 := hz.eq_of_src _ _
    change G.map ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Holomorphic.SheafComplex.sheafComplex E M) r).d n (n + 1)) = 0
    rw [hd]
    rfl
  have hLS : L.d n (n + 1) = 0 := by
    have hz := Below.Hodge.filteredFormSheaf_isZero_below E M n r (by dsimp [r]; omega)
    have hd : (SmoothComplex.Hodge.filteredSmoothSheafComplex E M r).d n (n + 1) = 0 := hz.eq_of_src _ _
    change G.map ((SmoothComplex.Hodge.filteredSmoothSheafComplex E M r).d n (n + 1)) = 0
    rw [hd]
    rfl
  let φ := (shortComplexFunctor' _ (.up ℕ) n (n + 1) (n + 2)).map f
  have hφ2 : Mono φ.τ₂ := hm (n + 1) le_rfl
  have hφ3 : Mono φ.τ₃ := hm (n + 2) (by dsimp [r]; omega)
  have hq := StalkClosedLiftCriterion.Homology.stalk_short_quasiIso_of_local_lift (X := TopCat.of M) φ x hKS hLS
    (fun U y hy => ?_)
  · change QuasiIsoAt (((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex
      (.up ℕ)).map f) (n + 1)
    apply (quasiIsoAt_iff' _ n (n + 1) (n + 2)
      ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).mpr
    exact hq
  · change ((SmoothComplex.Hodge.filteredSmoothSheafComplex E M r).d (n + 1) (n + 2)).hom.app (op U) y = 0 at hy
    rw [SmoothComplex.Hodge.filteredSmoothSheafComplex_d] at hy
    exact BoundarySections.Hodge.filtered_boundary_section_lift E M U r (n + 1) le_rfl (Or.inr rfl) y hy

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Boundary.Hodge
