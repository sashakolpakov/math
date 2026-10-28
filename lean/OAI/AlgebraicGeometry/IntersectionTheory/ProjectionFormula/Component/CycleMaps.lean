import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

/-! # Cycle Maps -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

noncomputable section

/-! The native graded cycle maps for an actual integral component.
Embedding agrees with proper pushforward along the component inclusion. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

def embed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) (p : ℕ) :
    (X.componentVariety C).presentation.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle p :=
  Finsupp.lmapDomain ℚ ℚ (Image.supportImage X C p)

def restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] (X.componentVariety C).presentation.RationalDimensionCycle p :=
  Finsupp.lcomapDomain (Image.supportImage X C p) (Image.supportImage_injective X C p)

theorem restrict_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : X.RationalDimensionCycle p)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport p) :
    restrict X C p a A = a (Image.supportImage X C p A) := rfl

theorem embed_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (A : (X.componentVariety C).presentation.DimensionCycleSupport p) (r : ℚ) :
    embed X C p (Finsupp.single A r) = Finsupp.single (Image.supportImage X C p A) r :=
  Finsupp.mapDomain_single

theorem restrict_embed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : (X.componentVariety C).presentation.RationalDimensionCycle p) :
    restrict X C p (embed X C p a) = a :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ (Image.supportImage_injective X C p) a

theorem embed_eq_pushforward (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) : embed X C p = ProperCycleLinearity.cyclePushforward (Image.inclusion X C) p p := by
  apply Finsupp.lhom_ext
  intro A r
  rw [embed_single, ProperCycleLinearity.cyclePushforward_single]
  have he : ProperCycleLinearity.imageSupport (Image.inclusion X C) A.val = X.componentSupportImage C A.val := by
    apply irreducibleSetEquivPoints.injective
    exact (irreducibleSetEquivPoints.apply_symm_apply _).trans
      (X.componentSupportImage_genericPoint C A.val).symm
  have hd : (Image.inclusion X C).left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 1 :=
    Principal.ClosedSectionCycle.residueDegree_immersion (X.componentInclusion C) _
  rw [ProperCycleLinearity.cyclePushforwardGenerator, hd, Nat.cast_one, one_smul, he]
  have hp : X.supportCodimension (X.componentSupportImage C A.val) = p :=
    (Image.image_codimension X C A.val).trans A.property
  rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left hp]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem embed_preserves_relations (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier) (p : ℕ) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences (X.componentVariety C).presentation p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).comap (embed X C p) := by
  let : SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Image.component_relativeDimension X m C
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨W, hW, g, hg, rfl⟩ :=
    (Principal.ClosedSectionCycle.isPrincipalDivisor_iff (X.componentVariety C).presentation p d).mp hd
  change embed X C p _ ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
  rw [embed_eq_pushforward]
  exact PushforwardDescent.principalCycle_pushforward_mem (Image.inclusion X C) m m p p rfl W hW g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps
