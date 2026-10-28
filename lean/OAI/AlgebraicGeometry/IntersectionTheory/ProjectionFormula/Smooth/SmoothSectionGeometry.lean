import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Fundamental
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle

/-! # Smooth Section Geometry -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SmoothSectionGeometry

noncomputable section

/-! A closed section meets every smooth inverse-image cycle properly.
The only possible intersection support is the section image of the
original cycle support, with its exact codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral Y.carrier]
  (s : Y.toOver ⟶ X.toOver) [IsClosedImmersion s.left]
  (m n r : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : n + r = m)

omit [IsClosedImmersion s.left] in
theorem image_whole : ProperCycleLinearity.imageSupport s (Integral.Fundamental.whole Y) =
    Closed.ImmersionSupport.support (show Y.carrier ⟶ X.carrier from s.left) := by
  apply irreducibleSetEquivPoints.injective
  exact (irreducibleSetEquivPoints.apply_symm_apply _).trans
    ((congrArg s.left (Integral.Fundamental.whole_point Y)).trans
      (Closed.ImmersionSupport.support_point (show Y.carrier ⟶ X.carrier from s.left)).symm)

include hd in
theorem codimension : X.supportCodimension
    (Closed.ImmersionSupport.support (show Y.carrier ⟶ X.carrier from s.left)) = r := by
  have h := Closed.EmbeddingCycle.image_codimension s n m (Integral.Fundamental.whole Y)
  rw [image_whole, Integral.Fundamental.whole_codimension Y n] at h
  omega

def support : X.DimensionCycleSupport r :=
  ⟨Closed.ImmersionSupport.support (show Y.carrier ⟶ X.carrier from s.left), codimension s m n r hd⟩

theorem support_range : ((support s m n r hd).val : Set X.carrier) = Set.range s.left :=
  s.left.isClosedEmbedding.isClosed_range.closure_eq

variable (f : X.toOver ⟶ Y.toOver) (hs : s ≫ f = 𝟙 Y.toOver)

include hs in
omit [IsIntegral Y.carrier] [IsClosedImmersion s.left] in
theorem point (y : Y.carrier) : f.left (s.left y) = y :=
  congrArg (fun g : Y.toOver ⟶ Y.toOver => g.left y) hs

include hs in
theorem support_projection_isIso :
    IsIso (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support (show Y.carrier ⟶ X.carrier from s.left)) ≫ f.left) := by
  rw [Closed.ImmersionSupport.retraction_eq_inv (show Y.carrier ⟶ X.carrier from s.left)
    f.left (congrArg Over.Hom.left hs)]
  infer_instance

include hd hs in
theorem proper (p : ℕ) (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport p)
    (hA : (A.val : Set X.carrier) ⊆ f.left ⁻¹' (B.val : Set Y.carrier)) :
    Supports.ProperCycle.pairMeetsProperly X p r A (support s m n r hd) := by
  intro E hE
  have hEs : (E : Set X.carrier) ⊆ Set.range s.left := fun x hx =>
    (support_range s m n r hd) ▸ (hE hx).2
  let W := Closed.EmbeddingCycle.preimage s E hEs
  have hWB : W ≤ B.val := by
    intro y hy
    have h := hA (hE hy).1
    change f.left (s.left y) ∈ (B.val : Set Y.carrier) at h
    rwa [point s f hs y] at h
  have hdim := (Supports.codimension_strictAnti Y n).antitone hWB
  rw [B.property] at hdim
  have he := Closed.EmbeddingCycle.image_codimension s n m W
  rw [Closed.EmbeddingCycle.image_preimage] at he
  omega

include hd hs in
theorem intersection_support (p : ℕ) (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport p)
    (hA : (A.val : Set X.carrier) ⊆ f.left ⁻¹' (B.val : Set Y.carrier))
    (C : X.DimensionCycleSupport (p + r))
    (hC : (C.val : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (support s m n r hd).val) :
    C = Closed.EmbeddingCycle.supportImage s n m p (p + r) (by omega) B := by
  have hCs : (C.val : Set X.carrier) ⊆ Set.range s.left := fun x hx =>
    (support_range s m n r hd) ▸ (hC hx).2
  let W := Closed.EmbeddingCycle.supportPreimage s n m p (p + r) (by omega) C hCs
  have hWB : W.val ≤ B.val := by
    intro y hy
    have h := hA (hC hy).1
    change f.left (s.left y) ∈ (B.val : Set Y.carrier) at h
    rwa [point s f hs y] at h
  have he : W = B := by
    apply Subtype.ext
    by_contra hn
    have h := Supports.codimension_strictAnti Y n (lt_of_le_of_ne hWB hn)
    rw [W.property, B.property] at h
    exact Nat.lt_irrefl p h
  exact (Closed.EmbeddingCycle.supportImage_preimage s n m p (p + r) (by omega) C hCs).symm.trans
    (congrArg (Closed.EmbeddingCycle.supportImage s n m p (p + r) (by omega)) he)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SmoothSectionGeometry
