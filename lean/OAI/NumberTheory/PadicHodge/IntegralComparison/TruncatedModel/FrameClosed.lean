import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame

/-! # Frame Closed -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameClosed

noncomputable section

/-! The closed charts of the actual finite-level frames have exactly
the prescribed special-fiber opens as their images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem range_comp_iso {U V Z : Scheme} (a : U ⟶ V) [IsIso a] (b : V ⟶ Z) :
    Set.range (a ≫ b) = Set.range b := by
  change Set.range (b ∘ a) = _
  have hs : Function.Surjective a := a.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X U
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f U
local instance sourceAlgebra : Algebra (Truncated.Witt.Ring p k n) A :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X U
local instance targetAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ U)

local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p A C
  (Truncated.AffineModelFrame.reduction p k n X Y f U)
  (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp U hU)
  (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp U hU)

theorem local_isIso : IsIso (Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU).obj.mapToX := by
  change IsIso (Spec.map (CommRingCat.ofHom (e).symm.toRingHom))
  exact (Scheme.Spec.mapIso (e).toCommRingCatIso.op).symm.isIso_hom

theorem openImmersion : IsOpenImmersion (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj.mapToX := by
  let := local_isIso p k n X Y f hp U hU
  let := Truncated.AffineModelFrame.chart_open p k n X Y f hp U hU
  change IsOpenImmersion ((Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU).obj.mapToX ≫
    Truncated.AffineModelFrame.chart p k n X Y f hp U hU)
  exact IsOpenImmersion.comp _ _

theorem range : Set.range (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj.mapToX =
    (f ⁻¹ᵁ U : Set Y.left) := by
  let := local_isIso p k n X Y f hp U hU
  exact (range_comp_iso (Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU).obj.mapToX
    (Truncated.AffineModelFrame.chart p k n X Y f hp U hU)).trans
      (Truncated.AffineModelFrame.residue_affine p k n X Y f hp U hU).range_fromSpec

theorem ideal_generated : (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj.ideal =
    (Ideal.span {(p : WittVector p k)}).map (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj.base := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameClosed
