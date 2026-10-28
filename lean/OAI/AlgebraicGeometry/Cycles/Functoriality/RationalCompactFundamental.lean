import OAI.AlgebraicGeometry.Cycles.Functoriality.CoveringFundamental
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients

/-! # Rational Compact Fundamental -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.RationalCompactFundamental.Construction

noncomputable section

open _root_.CategoryTheory OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients
open scoped TensorProduct ChangeOfRings _root_.Manifold ContDiff

/-- Unit rational coefficient applied to an actual integral relative class. -/
def rationalizeRelativeClass (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n :=
  (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] a)

/-- Inverse scalar-extension comparison commutes with maps of pairs. -/
theorem rationalRelativeHomologyIso_inv_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (n : ℕ) :
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv ≫
      HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n =
    CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf n) ≫
      (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).inv := by
  apply (cancel_mono (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).hom).mp
  rw [Category.assoc, CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso_hom_naturality,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Unit rational coefficients commute with the genuine maps of pairs. -/
theorem rationalizeRelativeClass_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (n : ℕ) (a : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n
      (rationalizeRelativeClass X A n a) =
    rationalizeRelativeClass Y B n (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf n a) := by
  have h := ConcreteCategory.congr_hom (rationalRelativeHomologyIso_inv_naturality f hf n)
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] a)
  change HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n
      (rationalizeRelativeClass X A n a) =
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).inv
      ((CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf n))
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] a)) at h
  have ht := ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ)
    (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf n) (1 : ℚ) a
  exact h.trans (congrArg (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).inv ht)

/-- The canonical compact fundamental class with unit rational coefficient. -/
def rationalCompactFundamentalClass (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (K : Set M) (hK : IsCompact K) : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of M) Kᶜ (2 * d) :=
  rationalizeRelativeClass (TopCat.of M) Kᶜ (2 * d) (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK)

/-- Compact restriction of the rational locally finite fundamental class. -/
theorem rationalCompactFundamentalClass_eq_restriction
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (K : Set M) (hK : IsCompact K) :
    rationalCompactFundamentalClass d K hK =
      CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of M) K hK (2 * d)
        (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of M) (2 * d)
          (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M)) := by
  rw [AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients.locallyFiniteIntegralToRationalHomology_compactRestriction,
    CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction]
  rfl

/-- Every compact relative trace of a proper finite analytic covering
has the covering degree as its fundamental-class multiplicity. -/
theorem rationalCompactFundamentalClass_map_degree
    (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree)
    (K : Set N) (hK : IsCompact K) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) (2 * d)
      (rationalCompactFundamentalClass d (f ⁻¹' K) (hp.isCompact_preimage hK)) =
    (degree : ℚ) • rationalCompactFundamentalClass d K hK := by
  rw [rationalCompactFundamentalClass_eq_restriction,
    rationalCompactFundamentalClass_eq_restriction]
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction_naturality ℚ f hp K hK (2 * d))
    (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of M) (2 * d)
      (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M))
  change CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ (TopCat.of N) K hK (2 * d)
      (CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hp (2 * d)
        (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of M) (2 * d)
          (CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass d M))) = _ at h
  rw [CoveringFundamental.Construction.rational_locallyFinite_push_fundamental_degree d f hp hl degree hdegree, map_smul] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.RationalCompactFundamental.Construction
