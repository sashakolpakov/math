import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle

/-! # Section Pair -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionPair

noncomputable section

/-! Proper intersection with an arbitrary cycle on a closed section
commutes with smooth pullback, as an equality of native cycles. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (s : Y.toOver ⟶ X.toOver) [IsClosedImmersion s.left]
  (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)] (hs : s ≫ f = 𝟙 Y.toOver)
  (m n r : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : n + r = m) (p q : ℕ) (B : Y.DimensionCycleSupport p) (D : Y.DimensionCycleSupport q)
  (hBD : Supports.ProperCycle.pairMeetsProperly Y p q B D)

local instance : IsLocallyNoetherian Y.toOver.left := inferInstanceAs (IsLocallyNoetherian Y.carrier)

include hs hd hBD in
theorem proper : Supports.ProperCycle.pairMeetsProperly X p (q + r) (Integral.FiberCycles.support f m n p B)
    (Closed.EmbeddingCycle.supportImage s n m q (q + r) (by omega) D) := by
  intro E hE
  have hEs : (E : Set X.carrier) ⊆ Set.range s.left := by
    intro x hx
    have h := (hE hx).2
    change x ∈ (ProperCycleLinearity.imageSupport s D.val : Set X.carrier) at h
    rw [ProperCycleLinearity.imageSupport_eq_image] at h
    exact ⟨h.choose, h.choose_spec.2⟩
  let W := Closed.EmbeddingCycle.preimage s E hEs
  have hW : (W : Set Y.carrier) ⊆ (B.val : Set Y.carrier) ∩ D.val := by
    intro y hy
    have h := hE hy
    have hb : f.left (s.left y) ∈ (B.val : Set Y.carrier) := by
      have he := h.1
      change s.left y ∈
        (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) B.val : Set X.carrier) at he
      rwa [Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_coe] at he
    rw [SmoothSectionGeometry.point s f hs] at hb
    have he := h.2
    change s.left y ∈ (ProperCycleLinearity.imageSupport s D.val : Set X.carrier) at he
    rw [ProperCycleLinearity.imageSupport_eq_image] at he
    obtain ⟨z, hz, hzy⟩ := he
    exact ⟨hb, s.left.isClosedEmbedding.injective hzy ▸ hz⟩
  have hb := hBD W hW
  have he := Closed.EmbeddingCycle.image_codimension s n m W
  rw [Closed.EmbeddingCycle.image_preimage] at he
  omega

include hs hd hBD in
theorem pair : Supports.ProperCycle.pairCycle X m p (q + r) (Integral.FiberCycles.support f m n p B)
    (Closed.EmbeddingCycle.supportImage s n m q (q + r) (by omega) D) =
    Closed.EmbeddingCycle.Maps.embed s n m (p + q) (p + (q + r)) (by omega)
      (Supports.ProperCycle.pairCycle Y n p q B D) := by
  let a := Supports.ProperCycle.pairCycle X m p (q + r) (Integral.FiberCycles.support f m n p B)
    (Closed.EmbeddingCycle.supportImage s n m q (q + r) (by omega) D)
  have ha : ∀ C ∈ a.support, (C.val : Set X.carrier) ⊆ Set.range s.left := by
    intro C hC
    have hn := Finsupp.mem_support_iff.mp hC
    rw [Supports.ProperCycle.pairCycle_apply X m p (q + r) _ _ (proper s f hs m n r hd p q B D hBD)] at hn
    have hc : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈
        ((Integral.FiberCycles.support f m n p B).val : Set X.carrier) ∩ ProperCycleLinearity.imageSupport s D.val := by
      by_contra h
      exact hn (dite_eq_right h)
    have hsub := (Supports.supportPoint_mem_iff_subset
      (⟨(ProperCycleLinearity.imageSupport s D.val : Set X.carrier), (ProperCycleLinearity.imageSupport s D.val).isClosed⟩ : Closeds X.carrier) C.val).mp hc.2
    intro x hx
    have hi := hsub hx
    change x ∈ (ProperCycleLinearity.imageSupport s D.val : Set X.carrier) at hi
    rw [ProperCycleLinearity.imageSupport_eq_image] at hi
    exact ⟨hi.choose, hi.choose_spec.2⟩
  have he : Closed.EmbeddingCycle.Maps.restrict s n m (p + q) (p + (q + r)) (by omega) a =
      Supports.ProperCycle.pairCycle Y n p q B D := by
    ext C
    rw [Closed.EmbeddingCycle.Maps.restrict_apply,
      Supports.ProperCycle.pairCycle_apply X m p (q + r) _ _ (proper s f hs m n r hd p q B D hBD),
      Supports.ProperCycle.pairCycle_apply Y n p q B D hBD]
    exact SectionMultiplicity.multiplicity s f hs m n B.val D.val C.val
  exact (Closed.EmbeddingCycle.Maps.embed_restrict s n m (p + q) (p + (q + r)) (by omega) a ha).symm.trans
    (congrArg (Closed.EmbeddingCycle.Maps.embed s n m (p + q) (p + (q + r)) (by omega)) he)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionPair
