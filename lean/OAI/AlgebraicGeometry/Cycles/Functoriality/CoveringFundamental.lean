import OAI.AlgebraicGeometry.Cycles.Functoriality.FiniteFundamental
import OAI.AlgebraicGeometry.Cycles.Functoriality.LocalOrientation
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients

/-! # Covering Fundamental -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CoveringFundamental.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality.Cycles OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients
open scoped _root_.Manifold ContDiff

/-- The actual relative homology map from a fiber's complement to
the complement of its image point. -/
def fiberHomologyPushforward {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X (f ⁻¹' {y}) n ⟶ CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology Y y n :=
  CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' {y})ᶜ) (B := {y}ᶜ) (fun _ hx => hx) n

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
variable [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]

/-- One analytic sheet contributes exactly one canonical local generator
to the pushforward at its target point. -/
theorem localSheet_push_generator
    (f : TopCat.of M ⟶ TopCat.of N)
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω)
    (he : Set.EqOn f e e.source) (x : LocalOrientation.Construction.analyticPartialSource e) (y : N)
    (hxy : f x.val = y)
    (hUK : ∀ z : LocalOrientation.Construction.analyticPartialSource e, z.val ∈ f ⁻¹' {y} → z = x) :
    fiberHomologyPushforward f y (2 * d)
      (FiniteFundamental.Construction.finiteSupportLocalInsertion (f ⁻¹' {y}) (LocalOrientation.Construction.analyticPartialSource e) x hUK (2 * d)
        (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := LocalOrientation.Construction.analyticPartialSource e) x)) =
    CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  let i : TopCat.of (LocalOrientation.Construction.analyticPartialSource e) ⟶ TopCat.of M :=
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (LocalOrientation.Construction.analyticPartialSource e : Set M)
  have hi : Set.MapsTo i ({x} : Set (LocalOrientation.Construction.analyticPartialSource e))ᶜ (f ⁻¹' {y})ᶜ :=
    fun z hz hzK => hz (hUK z hzK)
  have hf : Set.MapsTo f (f ⁻¹' {y})ᶜ ({y} : Set N)ᶜ := fun _ hx => hx
  have hfe : i ≫ f = LocalOrientation.Construction.analyticPartialSourceMap d e := by
    ext z
    exact he z.property
  have hey : e x.val = y := (he x.property).symm.trans hxy
  have hmaps : FiniteFundamental.Construction.finiteSupportLocalInsertion (f ⁻¹' {y}) (LocalOrientation.Construction.analyticPartialSource e) x hUK
      (2 * d) ≫ fiberHomologyPushforward f y (2 * d) =
      CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (LocalOrientation.Construction.analyticPartialSourceMap d e)
        (LocalOrientation.Construction.analyticPartialSourceMap_injective d e) x y hey (2 * d) :=
    (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hf (2 * d)).trans
      (CycleClass.Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ (2 * d))
  exact (ConcreteCategory.congr_hom hmaps
    (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := LocalOrientation.Construction.analyticPartialSource e) x)).trans
      (LocalOrientation.Construction.complexCanonicalLocalClass_partialSourceMap_to d e x y hey)

/-- The local pushforward of a finite fiber's fundamental class is its
cardinality times the canonical target generator. -/
theorem fiberHomologyPushforward_fundamental
    (f : TopCat.of M ⟶ TopCat.of N)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (y : N) (hfinite : (f ⁻¹' {y}).Finite) :
    fiberHomologyPushforward f y (2 * d)
      (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (f ⁻¹' {y}) hfinite.isCompact) =
    Nat.card (f ⁻¹' {y}) • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  classical
  let K : Set M := f ⁻¹' {y}
  let : Fintype K := hfinite.fintype
  choose e hx he using fun x : K => hl x.val
  let U : K → Opens M := fun x => LocalOrientation.Construction.analyticPartialSource (e x)
  have hxU : ∀ x : K, x.val ∈ U x := hx
  have hUK : ∀ (x : K) (z : U x), z.val ∈ K → z.val = x.val := by
    intro x z hz
    apply (e x).toPartialEquiv.injOn z.property (hx x)
    exact (he x z.property).symm.trans
      ((show f z.val = y from hz).trans
        ((show f x.val = y from x.property).symm.trans (he x (hx x))))
  rw [← FiniteFundamental.Construction.complexCompactFundamentalClass_finite_sum d K U hxU hUK, map_sum]
  calc
    _ = ∑ _x : K, CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
      apply Finset.sum_congr rfl
      intro x _
      exact localSheet_push_generator d f (e x) (he x) ⟨x.val, hxU x⟩ y x.property _
    _ = Nat.card K • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable [SecondCountableTopology M]

/-- At every target point, proper pushforward of the locally finite
fundamental class has multiplicity equal to the actual fiber cardinality. -/
theorem locallyFinite_push_fundamental_atPoint
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f) (y : N) :
    CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of N) y (2 * d)
      (CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hp (2 * d)
        (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)) =
    Nat.card (f ⁻¹' {y}) • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  have hn := CycleClass.Geometric.LocallyFiniteRestrictionNaturality.Cycles.locallyFiniteCompactHomologyRestriction_naturality_apply f hp {y}
    isCompact_singleton (2 * d) (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)
  have hr := CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction d M (f ⁻¹' {y})
    (hp.isCompact_preimage isCompact_singleton)
  exact hn.trans ((congrArg (fiberHomologyPushforward f y (2 * d)) hr).trans
    (fiberHomologyPushforward_fundamental d f hl y
      (Covering.Construction.finite_fiber_of_proper_localHomeomorph f hp hl.isLocalHomeomorph y)))

variable [SecondCountableTopology N]

/-- A proper analytic local diffeomorphism with `degree` points in each
fiber sends the fundamental class to `degree` times the target class. -/
theorem locallyFinite_push_fundamental_degree
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree) :
    CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hp (2 * d)
      (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M) =
    degree • CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d N := by
  apply CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteHomology_point_ext d N
  intro y
  rw [map_nsmul, CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_atPoint,
    locallyFinite_push_fundamental_atPoint d f hp hl y, hdegree y]

/-- The degree formula with the actual rational coefficient-change map,
matching the coefficients used by geometric cycle classes. -/
theorem rational_locallyFinite_push_fundamental_degree
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree) :
    CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hp (2 * d)
      (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of M) (2 * d)
        (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)) =
    (degree : ℚ) • AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of N) (2 * d)
      (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d N) := by
  rw [AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology_naturality,
    locallyFinite_push_fundamental_degree d f hp hl degree hdegree,
    map_nsmul, Nat.cast_smul_eq_nsmul]

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CoveringFundamental.Construction
