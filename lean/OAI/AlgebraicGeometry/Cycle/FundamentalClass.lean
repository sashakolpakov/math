/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Cohomology.WithSupport
import OAI.AlgebraicGeometry.Cycle.ComponentSupportIsoHom
import OAI.AlgebraicGeometry.Cycle.SmoothSupportCoclassSection
import OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison

/-! # Fundamental Class -/

namespace OAI.AlgebraicGeometry

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular
open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is transported to the
supported cohomology sheaf. Lowest-degree purity and unique extension across the singular
boundary then give a supported class on the original ambient variety, and forgetting its support
lands in ordinary rational cohomology.

The corresponding Borel–Moore fundamental class is obtained through the complex-orientation
duality for the ambient chain sheaf. Compactification independence and rational-equivalence
invariance are separate statements.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local instance ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint X) := ComplexPoint.Basic.Point.analyticTopology

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `S ⊆ X(ℂ)` closed. For a natural
number `n`, this identifies the degree-`n` cohomology sheaf of `Γ_S(I^•)` with the
sheafification of `V ↦ H^n(V, V \ S; ℚ)`. Here `ℚ → I^•` is an injective resolution and `Γ_S`
takes sections vanishing off `S`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ) :
    -- The `n`-th cohomology sheaf of `RΓ_S(ℚ)`.
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      𝓗_[S]^n(TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X); ℚ) :=
  letI : ∀ V : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  (asIso (HomologicalComplex.homologyMap
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed n

section

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. For a natural number `p`, this is `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`,
computed from global sections of the subsheaves supported in `Z(ℂ)` of a chosen injective
resolution of the constant rational sheaf. -/
abbrev ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, with `Z` the subvariety with generic point `x`.
  (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    -- Global sections, i.e. sections over all of `X(ℂ)`.
    ⊤).mapHomologicalComplex ℤᵘᵖ).obj
    -- `RΓ_{Z(ℂ)}(ℚ)`.
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
      -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).homology
    -- Degree `2p`.
    (2 * (p : ℤ))

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and `𝓗^{2p}_S` for the
sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. For a natural number `p`, this is the abelian group
`Γ(U, 𝓗^{2p}_S)` of sections of the local relative-cohomology sheaf away from the singular locus
of `Z`. -/
abbrev ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (𝓗_[Cycle.Support.cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X); ℚ)).presheaf.obj
      -- The open `X(ℂ) \ Z_sing(ℂ)`.
      (op (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This is the isomorphism
`H^{2p}_S(X(ℂ); ℚ) ≅ Γ(U, 𝓗^{2p}_S)`. It restricts a supported class to `U` and takes its local
relative classes. Purity on the smooth locus and vanishing of cohomology supported on the
singular locus make the map invertible. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso :
    ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p ≅ ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections X x p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx ≪≫
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫
      (he ▸ (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)).mapIso
          (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X
            (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (2 * p)))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This additive map `Γ(U,
𝓗^{2p}_S) → H^{2p}_S(X(ℂ); ℚ)` assigns to a section its unique supported class on all of `X(ℂ)`.
It inverts restriction followed by passage to local relative-cohomology classes. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentExtendSmoothCoclass :
    ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSmoothCoclassSections X x p →+ ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` computed from
sections supported on `Z(ℂ)` of an injective resolution of the constant rational sheaf. Its
local classes along the smooth locus of `Z` evaluate to `1` on the complex orientation classes
of the normal spaces. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass : ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  ComplexPoint.Basic.ComplexSchemePoint.cycleComponentExtendSmoothCoclass X x hx
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus of `Z` evaluate to `1` on the complex orientation classes of the normal
spaces. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    H_[ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) :=
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
    (2 * p)).symm (he ▸ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportedInjectiveClass X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. The fundamental cohomology class `[Z] ∈ H^{2p}(X(ℂ);ℚ)` is
obtained by forgetting the support of the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus evaluate to `1` on the complex orientation classes of the normal spaces. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass : H^(2 * p)(X; ℚ) :=
  ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (2 * p)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafSupportedClass X x hx)

end

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `p` a natural number. This is the
rational subspace of `H^{2p}(X(ℂ); ℚ)` spanned by the fundamental cohomology classes of all
codimension-`p` integral closed subvarieties of `X`. Their classes are normalized by the complex
orientations of their normal spaces on their smooth loci. -/
def ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan (p : ℕ) : Submodule ℚ (H^(2 * p)(X; ℚ)) :=
  sSup {Submodule.span ℚ {ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X x hx} |
    (x : X.left) (hx : Order.coheight x = p) }

end

end OAI.AlgebraicGeometry
