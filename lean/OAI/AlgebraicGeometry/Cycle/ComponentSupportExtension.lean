/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Stratification.LocalSupportVanishing
import OAI.AlgebraicGeometry.Cycle.ComponentSmoothIsoHom
import OAI.AlgebraicTopology.Support.FiniteFiltrationVanishing

/-! # Component Support Extension -/

namespace OAI.AlgebraicGeometry.Cycle.ComponentSupportExtension.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Unique extension across a cycle component's singular boundary

The canonical finite smooth filtration and its layerwise vanishing give the singular
boundary zero supported cohomology below `2(p+1)`, in particular in degrees `2p` and
`2p+1`. The nested-support localization sequence then makes restriction from the full
component support to its smooth-locus ambient open an isomorphism in degree `2p`, whose
inverse is the unique extension operation.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`, where `Z_sing,k` is the `k`-th stage of
the finite smooth filtration of `Z_sing` (so `Z_sing,0 = Z_sing`). -/
private theorem cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ ComponentSingularGe.cycleComponentSingularFiltrationLength X x)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ)`, for the `k`-th stage of the singular filtration.
    IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing,k(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        -- `Z_sing,k(ℂ)`, as a closed subset of `X(ℂ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  let O (j : ℕ) := (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_antitone X x hab hyb)
  have hN : O (ComponentSingularGe.cycleComponentSingularFiltrationLength X x) = ⊤ := by
    dsimp only [O]
    rw [ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint.Basic.ComplexSchemePoint X))) ↔ y ∈ Set.univ
    simp
  exact AlgebraicTopology.Support.FiniteFiltrationVanishing.TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) O hO (ComponentSingularGe.cycleComponentSingularFiltrationLength X x) hN
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)
    (fun j => AlgebraicTopology.Sheaf.InjectiveFlasque.TopCat.injective_isFlasque _ _) n
    (fun j _ => ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayerSectionCohomology_isZero_of_lt
      X x hx j n hn) k hk

include hx in
/-- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`. -/
private theorem cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) :=
  cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt X x hx
    0 (Nat.zero_le _) n hn

include hx in
/-- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree :
    -- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0))).homology
      -- Degree `2p`.
      (2 * (p : ℤ))) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega)

include hx in
/-- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
private theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ :
    -- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0))).homology
      -- Degree `2p + 1`.
      (2 * (p : ℤ) + 1)) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega)

/-- Every point of the singular boundary belongs to the full component support. -/
private theorem cycleComponentSingularBoundary_le_support :
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x 0 ≤ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x := by
  intro y hy
  obtain ⟨z, _, hz⟩ := hy
  change y.underlying ∈ closure ({x} : Set X.left)
  rw [← SupportEq.range_cycleComponentι X.left x]
  exact ⟨z, hz⟩

/-- The complement inclusion determining the localization sequence. -/
private theorem cycleComponentSupportComplement_le_smoothAmbientOpen :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x).compl ≤ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x :=
  fun _ hy hyS ↦ hy (cycleComponentSingularBoundary_le_support X x hyS)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Let `I^•` be the chosen injective resolution of `ℚ` on `X(ℂ)`.
This restricts sections of its subsheaves supported in `Z(ℂ)` from all of `X(ℂ)` to `X(ℂ) \
Z_sing(ℂ)`, degree by degree. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction :
    -- Restriction `RΓ_{Z(ℂ)}(X(ℂ)) → RΓ_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ))`.
    ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)) ⟶
    ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)) :=
  AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)) (homOfLE le_top)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hx in
/-- Restriction `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)` is an isomorphism:
in the localization sequence for `Z_sing(ℂ) ⊆ Z(ℂ)`, the neighbouring terms
`H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)` and `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)` vanish. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction_homology_isIso :
    IsIso (HomologicalComplex.homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ))) := by
  let T := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)
  let h := cycleComponentSupportComplement_le_smoothAmbientOpen X x
  let K := ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X
  let S := AlgebraicTopology.Support.NestedLocalization.TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex T h ⊤ K
  let := AlgebraicTopology.Support.NestedLocalization.TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing T h ⊤ K
    (2 * (p : ℤ))
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree X x hx)
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ X x hx)
  have he : HomologicalComplex.homologyMap S.g (2 * (p : ℤ)) ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Support.NestedOnOpen.TopCat.Sheaf.nestedSupportRestrictionLastComplexIso T h K).hom (2 * (p : ℤ)) =
    HomologicalComplex.homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 * (p : ℤ)))
      (AlgebraicTopology.Support.NestedOnOpen.TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g T h K)
  rw [← he]
  infer_instance

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Restriction to `U = X(ℂ) \ Z_sing(ℂ)` gives this
isomorphism `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) ≅ H^{2p}_{Z(ℂ) ∩ U}(U; ℚ)`. Its inverse extends a class
uniquely across the singular locus, whose supported cohomology vanishes in degrees `2p` and
`2p+1`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
      -- Degree `2p`.
      (2 * (p : ℤ))) ≅
    -- `H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`.
    ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
          -- Degree `2p`.
          (2 * (p : ℤ))) :=
  letI := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction_homology_isIso X x hx
  asIso (HomologicalComplex.homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)))

end

end OAI.AlgebraicGeometry.Cycle.ComponentSupportExtension.ComplexPoint
