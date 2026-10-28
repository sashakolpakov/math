import OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup

/-! # Compact Fiber Slant -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions

/-! Integration over a compact fiber support is compatible with enlarging that support. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem rationalCompactFundamental_restriction (K L : Set M)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (𝟙 (TopCat.of M))
      (A := Lᶜ) (B := Kᶜ) (fun _ hx hk => hx (hKL hk))) (2 * d)
      (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d L hL) = ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK := by
  refine (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalizeRelativeClass_naturality (𝟙 (TopCat.of M))
    (A := Lᶜ) (B := Kᶜ) (fun _ hx hk => hx (hKL hk)) (2 * d)
    (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d L hL)).trans ?_
  exact congrArg (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalizeRelativeClass (TopCat.of M) Kᶜ (2 * d))
    (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_restriction d K L hK hL hKL)

def integrate (X : TopCat.{0}) (A : Set X) (K : Set M) (hK : IsCompact K) (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A Kᶜ) (p + 2 * d) →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p :=
  Relative.Slant.Constructions.slant ℚ X (TopCat.of M) A Kᶜ p (2 * d) (p + 2 * d) rfl
    (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK)

theorem integrate_enlargement (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A Kᶜ) (p + 2 * d)) :
    integrate d X A L hL p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
        (A := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A Lᶜ)
        (B := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A Kᶜ)
        (fun _ hx => hx.elim Or.inl (fun hz => Or.inr (fun hk => hz (hKL hk))))
        (p + 2 * d) c) = integrate d X A K hK p c := by
  have h := Relative.SlantNaturality.Constructions.slant_natural ℚ (𝟙 X) (𝟙 (TopCat.of M))
    (A := A) (A' := A) (B := Lᶜ) (B' := Kᶜ)
    (fun _ hx => hx) (fun _ hx hk => hx (hKL hk)) p (2 * d) (p + 2 * d) rfl
    (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d L hL) c
  rw [rationalCompactFundamental_restriction d K L hK hL hKL] at h
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at h
  exact h

end AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection

/-! Integrating a class with an arbitrary support contained in a product.
The result is independent of the chosen compact bound in the fiber. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

omit [T2Space M] in
theorem boundedComplementMapsTo (X : TopCat.{0}) (S : Set X) (K : Set M) (T : Set (X × M))
    (hT : T ⊆ S ×ˢ K) :
    Set.MapsTo (𝟙 (TopCat.of (X × M))) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) Sᶜ Kᶜ) Tᶜ := by
  intro z hz ht
  exact hz.elim (fun hs => hs (hT ht).1) (fun hk => hk (hT ht).2)

def projectSupported (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T : Set (X × M)) (hT : T ⊆ S ×ˢ K) (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ (p + 2 * d) →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Sᶜ p :=
  (integrate d X Sᶜ K hK p).comp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
      (boundedComplementMapsTo X S K T hT) (p + 2 * d)).hom

theorem projectSupported_enlargement (X : TopCat.{0}) (S : Set X) (T : Set (X × M)) (p : ℕ)
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hT : T ⊆ S ×ˢ K) (hT' : T ⊆ S ×ˢ L)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ (p + 2 * d)) :
    projectSupported d X S L hL T hT' p c = projectSupported d X S K hK T hT p c := by
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of (X × M))) (𝟙 (TopCat.of (X × M)))
      (A := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) Sᶜ Lᶜ)
      (B := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) Sᶜ Kᶜ) (C := Tᶜ)
      (fun _ hx => hx.elim Or.inl (fun hz => Or.inr (fun hk => hz (hKL hk))))
      (boundedComplementMapsTo X S K T hT) (p + 2 * d)) c
  refine (congrArg (integrate d X Sᶜ L hL p) hc).symm.trans ?_
  exact integrate_enlargement d X Sᶜ p K L hK hL hKL
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
      (boundedComplementMapsTo X S K T hT) (p + 2 * d) c)

theorem projectSupported_independent (X : TopCat.{0}) (S : Set X) (T : Set (X × M)) (p : ℕ)
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (hT : T ⊆ S ×ˢ K) (hT' : T ⊆ S ×ˢ L) :
    projectSupported d X S K hK T hT p = projectSupported d X S L hL T hT' p := by
  have hU : T ⊆ S ×ˢ (K ∪ L) := fun z hz => ⟨(hT hz).1, Or.inl (hT hz).2⟩
  ext c
  exact (projectSupported_enlargement d X S T p K (K ∪ L) hK (hK.union hL)
    Set.subset_union_left hT hU c).symm.trans
    (projectSupported_enlargement d X S T p L (K ∪ L) hL (hK.union hL)
      Set.subset_union_right hT' hU c)

end AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection

end

end OAI
