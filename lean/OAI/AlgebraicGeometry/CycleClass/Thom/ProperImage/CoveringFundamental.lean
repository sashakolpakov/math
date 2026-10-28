import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FiniteFundamental
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.LocalOrientation
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients

/-! # Covering Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CoveringFundamental.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality.Cycles OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients
open scoped _root_.Manifold ContDiff

/-- The actual relative homology map from a fiber's complement to
the complement of its image point. -/
def fiberHomologyPushforward {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X (f ⁻¹' {y}) n ⟶ Geometric.LocalHomology.Cycles.localSingularHomology Y y n :=
  Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' {y})ᶜ) (B := {y}ᶜ) (fun _ hx => hx) n

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
variable [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]

/-- One analytic sheet contributes exactly one canonical local generator
to the pushforward at its target point. -/
theorem localSheet_push_generator
    (f : TopCat.of M ⟶ TopCat.of N)
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω)
    (he : Set.EqOn f e e.source) (x : LocalOrientation.Constructions.Construction.analyticPartialSource e) (y : N)
    (hxy : f x.val = y)
    (hUK : ∀ z : LocalOrientation.Constructions.Construction.analyticPartialSource e, z.val ∈ f ⁻¹' {y} → z = x) :
    fiberHomologyPushforward f y (2 * d)
      (FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion (f ⁻¹' {y}) (LocalOrientation.Constructions.Construction.analyticPartialSource e) x hUK (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := LocalOrientation.Constructions.Construction.analyticPartialSource e) x)) =
    Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  let i : TopCat.of (LocalOrientation.Constructions.Construction.analyticPartialSource e) ⟶ TopCat.of M :=
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (LocalOrientation.Constructions.Construction.analyticPartialSource e : Set M)
  have hi : Set.MapsTo i ({x} : Set (LocalOrientation.Constructions.Construction.analyticPartialSource e))ᶜ (f ⁻¹' {y})ᶜ :=
    fun z hz hzK => hz (hUK z hzK)
  have hf : Set.MapsTo f (f ⁻¹' {y})ᶜ ({y} : Set N)ᶜ := fun _ hx => hx
  have hfe : i ≫ f = LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e := by
    ext z
    exact he z.property
  have hey : e x.val = y := (he x.property).symm.trans hxy
  have hmaps : FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion (f ⁻¹' {y}) (LocalOrientation.Constructions.Construction.analyticPartialSource e) x hUK
      (2 * d) ≫ fiberHomologyPushforward f y (2 * d) =
      Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e)
        (LocalOrientation.Constructions.Construction.analyticPartialSourceMap_injective d e) x y hey (2 * d) :=
    (Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hf (2 * d)).trans
      (Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ (2 * d))
  exact (ConcreteCategory.congr_hom hmaps
    (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := LocalOrientation.Constructions.Construction.analyticPartialSource e) x)).trans
      (LocalOrientation.Constructions.Construction.complexCanonicalLocalClass_partialSourceMap_to d e x y hey)

/-- The local pushforward of a finite fiber's fundamental class is its
cardinality times the canonical target generator. -/
theorem fiberHomologyPushforward_fundamental
    (f : TopCat.of M ⟶ TopCat.of N)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (y : N) (hfinite : (f ⁻¹' {y}).Finite) :
    fiberHomologyPushforward f y (2 * d)
      (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (f ⁻¹' {y}) hfinite.isCompact) =
    Nat.card (f ⁻¹' {y}) • Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  classical
  let K : Set M := f ⁻¹' {y}
  let : Fintype K := hfinite.fintype
  choose e hx he using fun x : K => hl x.val
  let U : K → Opens M := fun x => LocalOrientation.Constructions.Construction.analyticPartialSource (e x)
  have hxU : ∀ x : K, x.val ∈ U x := hx
  have hUK : ∀ (x : K) (z : U x), z.val ∈ K → z.val = x.val := by
    intro x z hz
    apply (e x).toPartialEquiv.injOn z.property (hx x)
    exact (he x z.property).symm.trans
      ((show f z.val = y from hz).trans
        ((show f x.val = y from x.property).symm.trans (he x (hx x))))
  rw [← FiniteFundamental.Constructions.Construction.complexCompactFundamentalClass_finite_sum d K U hxU hUK, map_sum]
  calc
    _ = ∑ _x : K, Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
      apply Finset.sum_congr rfl
      intro x _
      exact localSheet_push_generator d f (e x) (he x) ⟨x.val, hxU x⟩ y x.property _
    _ = Nat.card K • Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable [SecondCountableTopology M]

/-- At every target point, proper pushforward of the locally finite
fundamental class has multiplicity equal to the actual fiber cardinality. -/
theorem locallyFinite_push_fundamental_atPoint
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f) (y : N) :
    Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of N) y (2 * d)
      (Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hp (2 * d)
        (Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)) =
    Nat.card (f ⁻¹' {y}) • Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  have hn := Geometric.LocallyFiniteRestrictionNaturality.Cycles.locallyFiniteCompactHomologyRestriction_naturality_apply f hp {y}
    isCompact_singleton (2 * d) (Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)
  have hr := Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction d M (f ⁻¹' {y})
    (hp.isCompact_preimage isCompact_singleton)
  exact hn.trans ((congrArg (fiberHomologyPushforward f y (2 * d)) hr).trans
    (fiberHomologyPushforward_fundamental d f hl y
      (Covering.Constructions.Construction.finite_fiber_of_proper_localHomeomorph f hp hl.isLocalHomeomorph y)))

variable [SecondCountableTopology N]

/-- A proper analytic local diffeomorphism with `degree` points in each
fiber sends the fundamental class to `degree` times the target class. -/
theorem locallyFinite_push_fundamental_degree
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree) :
    Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hp (2 * d)
      (Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M) =
    degree • Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d N := by
  apply Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteHomology_point_ext d N
  intro y
  rw [map_nsmul, Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_atPoint,
    locallyFinite_push_fundamental_atPoint d f hp hl y, hdegree y]

/-- The degree formula with the actual rational coefficient-change map,
matching the coefficients used by geometric cycle classes. -/
theorem rational_locallyFinite_push_fundamental_degree
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree) :
    Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hp (2 * d)
      (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of M) (2 * d)
        (Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)) =
    (degree : ℚ) • AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of N) (2 * d)
      (Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d N) := by
  rw [AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology_naturality,
    locallyFinite_push_fundamental_degree d f hp hl degree hdegree,
    map_nsmul, Nat.cast_smul_eq_nsmul]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CoveringFundamental.Constructions.Construction
