import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents

/-! # Support Connecting Ambient -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

noncomputable section

/-!
# Ambient cochain formulas for support connecting representatives

The actual closed-support representatives have equal ambient differentials.
This is obtained by applying the proved relative-cochain inclusion maps to
the existing representative identities.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restricting the vanishing set of a relative cochain preserves its ambient cochain. -/
theorem relativeRationalSubsetCochainMap_inclusion_apply (X : TopCat.{0})
    {A B : Set X} (h : A ⊆ B) (n : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X n) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n
        ((SupportConnectingComponents.relativeRationalSubsetCochainMap X h).f n c) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n c :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (SupportConnectingComponents.relativeRationalSubsetCochainMap_inclusion X h) n) c

/-- Closed-support connecting representatives with both differential identities
expressed directly in the ambient rational cochain complex. -/
theorem supportConnecting_components_support_ambient (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) n) :
    ∃ (bK : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X n)
      (bL : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X n)
      (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) (n + 1)),
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f n bK -
          (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f n bL =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f n a.val ∧
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f (n + 1)
          ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).d n (n + 1) bK) =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (n + 1) c.val ∧
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f (n + 1)
          ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).d n (n + 1) bL) =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (n + 1) c.val ∧
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X K L hK hL n
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) n a) =
        Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) (n + 1) c := by
  obtain ⟨bK, bL, c, hdiff, hdK, hdL, hclass⟩ :=
    SupportConnectingComponents.supportConnecting_components_support X K L hK hL n a
  refine ⟨bK, bL, c, hdiff, ?_, ?_, hclass⟩
  · exact (congrArg ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f (n + 1)) hdK).trans
      (relativeRationalSubsetCochainMap_inclusion_apply X
        (show Kᶜ ⊆ (K ∩ L)ᶜ from fun _ hx h => hx h.1) (n + 1) c.val)
  · exact (congrArg ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f (n + 1)) hdL).trans
      (relativeRationalSubsetCochainMap_inclusion_apply X
        (show Lᶜ ⊆ (K ∩ L)ᶜ from fun _ hx h => hx h.2) (n + 1) c.val)

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient
