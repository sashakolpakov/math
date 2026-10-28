import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension

/-! # Embedding Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle

noncomputable section

section

/-! Native cycle supports under a closed embedding, with the actual
change of codimension and a support inverse on its image. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsClosedImmersion i.left]
  (m n : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension n X.structureMap]

theorem image_codimension (A : IrreducibleCloseds V.carrier) :
    X.supportCodimension (ProperCycleLinearity.imageSupport i A) + m = V.supportCodimension A + n := by
  have hd := PushforwardComposition.Grading.support_dimension_eq_of_degree i A (by
    rw [Principal.ClosedSectionCycle.residueDegree_immersion]
    exact Nat.one_ne_zero)
  have hv := Grading.supportDimension_add_codimension V m A
  have hx := Grading.supportDimension_add_codimension X n (ProperCycleLinearity.imageSupport i A)
  omega

def supportImage (p q : ℕ) (hdeg : p + n = q + m) (A : V.DimensionCycleSupport p) : X.DimensionCycleSupport q :=
  ⟨ProperCycleLinearity.imageSupport i A.val, by
    have he := image_codimension i m n A.val
    rw [A.property] at he
    omega⟩

theorem supportImage_injective (p q : ℕ) (hdeg : p + n = q + m) :
    Function.Injective (supportImage i m n p q hdeg) := by
  intro A B he
  apply Subtype.ext
  apply irreducibleSetEquivPoints.injective
  apply i.left.isClosedEmbedding.injective
  have hpoints := congrArg (fun D : X.DimensionCycleSupport q => CycleClass.Thom.IntersectionGeometry.supportPoint D.val) he
  exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans
    (hpoints.trans (irreducibleSetEquivPoints.apply_symm_apply _))

def preimage (B : IrreducibleCloseds X.carrier) (hB : (B : Set X.carrier) ⊆ Set.range i.left) :
    IrreducibleCloseds V.carrier := SupportDimension.preimage i.left B hB

omit [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension n X.structureMap] in
theorem image_preimage (B : IrreducibleCloseds X.carrier) (hB : (B : Set X.carrier) ⊆ Set.range i.left) :
    ProperCycleLinearity.imageSupport i (preimage i B hB) = B :=
  (Support.Map.imageClosure_eq i (preimage i B hB)).symm.trans
    (SupportDimension.imageClosure i.left B hB)

def supportPreimage (p q : ℕ) (hdeg : p + n = q + m) (B : X.DimensionCycleSupport q)
    (hB : (B.val : Set X.carrier) ⊆ Set.range i.left) : V.DimensionCycleSupport p :=
  ⟨preimage i B.val hB, by
    have he := image_codimension i m n (preimage i B.val hB)
    rw [image_preimage, B.property] at he
    omega⟩

theorem supportImage_preimage (p q : ℕ) (hdeg : p + n = q + m) (B : X.DimensionCycleSupport q)
    (hB : (B.val : Set X.carrier) ⊆ Set.range i.left) :
    supportImage i m n p q hdeg (supportPreimage i m n p q hdeg B hB) = B :=
  Subtype.ext (image_preimage i B.val hB)

end

/-! Closed embedding pushforward is the injective renaming of native
cycle supports. Its coefficient restriction is inverse on supported cycles. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Maps

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsClosedImmersion i.left]
  (m n : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension n X.structureMap]
  (p q : ℕ) (hdeg : p + n = q + m)

def embed : V.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle q :=
  Finsupp.lmapDomain ℚ ℚ (supportImage i m n p q hdeg)

def restrict : X.RationalDimensionCycle q →ₗ[ℚ] V.RationalDimensionCycle p :=
  Finsupp.lcomapDomain (supportImage i m n p q hdeg) (supportImage_injective i m n p q hdeg)

theorem restrict_apply (a : X.RationalDimensionCycle q) (A : V.DimensionCycleSupport p) :
    restrict i m n p q hdeg a A = a (supportImage i m n p q hdeg A) := rfl

theorem embed_single (A : V.DimensionCycleSupport p) (r : ℚ) :
    embed i m n p q hdeg (Finsupp.single A r) = Finsupp.single (supportImage i m n p q hdeg A) r :=
  Finsupp.mapDomain_single

theorem restrict_embed (a : V.RationalDimensionCycle p) :
    restrict i m n p q hdeg (embed i m n p q hdeg a) = a :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ (supportImage_injective i m n p q hdeg) a

theorem embed_eq_pushforward : embed i m n p q hdeg = ProperCycleLinearity.cyclePushforward i p q := by
  apply Finsupp.lhom_ext
  intro A r
  have hc : X.supportCodimension (ProperCycleLinearity.imageSupport i A.val) = q := (supportImage i m n p q hdeg A).property
  rw [embed_single, ProperCycleLinearity.cyclePushforward_single, ProperCycleLinearity.cyclePushforwardGenerator,
    Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, one_smul,
    CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left hc]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem embed_restrict (a : X.RationalDimensionCycle q)
    (ha : ∀ A ∈ a.support, (A.val : Set X.carrier) ⊆ Set.range i.left) :
    embed i m n p q hdeg (restrict i m n p q hdeg a) = a := by
  apply Finsupp.mapDomain_comapDomain _ (supportImage_injective i m n p q hdeg)
  intro A hA
  exact ⟨supportPreimage i m n p q hdeg A (ha A hA), supportImage_preimage i m n p q hdeg A (ha A hA)⟩

include hdeg in
theorem pushforward_injective : Function.Injective (ProperCycleLinearity.cyclePushforward i p q) := by
  rw [← embed_eq_pushforward i m n p q hdeg]
  exact (show Function.LeftInverse (restrict i m n p q hdeg) (embed i m n p q hdeg) from
    restrict_embed i m n p q hdeg).injective

end Maps

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle
