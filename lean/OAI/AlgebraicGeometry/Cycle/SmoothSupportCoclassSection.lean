/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.SmoothPairGerm
import OAI.AlgebraicGeometry.Cycle.ComponentSmoothIsoHom
import OAI.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

/-! # Smooth Support Coclass Section -/

namespace OAI.AlgebraicGeometry

noncomputable section

open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular

open _root_.AlgebraicGeometry

/-!
# The normalized component coclass on the original ambient smooth-support open

The component's smooth locus is closed in the complement of its singular boundary. Its exactly
normalized smooth-support section there is transported through the analytic open embedding,
giving a section of the original ambient relative-cohomology sheaf on the singular-boundary
complement.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.Topology Opposite
open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- The dimension of the smooth locus, bundled over `Spec ℂ`. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x).hom :=
  Cycle.ComponentSmoothCoe.cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx

include X hx in
omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The codimension arithmetic, from the coheight bound. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension :
    Topology.Dimension.Basic.TopologicalSpace.dim X.left - (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) = p := by
  have h := AlgebraicGeometry.Smooth.DimensionFormula.SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
  rw [hx] at h
  have hpd : p ≤ Topology.Dimension.Basic.TopologicalSpace.dim X.left := by exact_mod_cast h
  omega

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. On the analytic space of the open scheme `X \
Z_sing`, this is the global section of the sheafification of `V ↦ H^{2p}(V, V \ Z_reg(ℂ); ℚ)`
obtained by gluing local normal orientation coclasses. The local class is normalized to pair to
`1` with the orientation class of the complex normal space. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftCoclassSection :
    -- The support is the image of `Z_reg`; if `Z ⊆ X` is the variety, the ambient space is the
    -- `X \ Z_sing` open, as a complex manifold.
    (𝓗_[Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * p)
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
      (op ⊤) :=
  letI := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLift_codimension X x hx
  hdeg ▸ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection
    (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x)
    (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x) (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p) (Topology.Dimension.Basic.TopologicalSpace.dim X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the continuous map `(X \ Z_sing)(ℂ) → X(ℂ)` induced by
inclusion of the open subscheme. It identifies its source with the analytic open subset `X(ℂ) \
Z_sing(ℂ)`. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint.Basic.ComplexSchemePoint (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x)) ⟶
    TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X) :=
  TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap
    (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)))

omit [IsIntegral X.left] [Smooth X.hom] in
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x) :=
  ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpen X x)

/-- Support membership is transported by the lift-image theorem. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support :
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' Cycle.Support.cycleComponentSupport X x =
      Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ =
      ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x := by
  apply Opens.ext
  change (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x) '' Set.univ = _
  rw [Set.image_univ]
  exact ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusAmbientOpen_analytic_image X x

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This section of `𝓗^{2p}_S` on
`U` is obtained by gluing the local coclasses defined by complex normal coordinates along
`Z_reg(ℂ)`. The local class is normalized to pair to `1` with the orientation class of the
complex normal space. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection :
    -- The support is `Z(ℂ)`, the complex points of the subvariety, inside `X(ℂ)`.
    (𝓗_[Cycle.Support.cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X); ℚ)).presheaf.obj
      -- The open set of complex points of the complement of the singular boundary, i.e. `X(ℂ) \ Z_sing(ℂ)`.
      (op (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)) :=
  AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOnOpen (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (Cycle.Support.cycleComponentSupport X x)
    (Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x)))
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftCoclassSection X x hx)

end

end OAI.AlgebraicGeometry
