import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantSheafNaturality

/-! # Constant Inverse Image Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantInverseImageNaturality

noncomputable section

/-! # The genuine constant inverse-image isomorphism

The constant transport used in original hypercohomology is adjoint to the
actual coefficient identity on sheafified constants.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the actual constant pullback is the original constant-sheaf unit. -/
theorem originalConstantSheafPullback_homEquiv (f : X ⟶ Y) (A : AddCommGrpCat) :
    (constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      AddCommGrpCat isTerminalTop).homEquiv A _ (ConstantPullback.originalConstantSheafPullback f A) =
    (constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat isTerminalTop).unit.app A := by
  unfold constantSheafAdj
  rw [Adjunction.comp_homEquiv]
  change (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) A) ≫
        ConstantPullback.originalConstantSheafPullbackHom f A).app (Opposite.op ⊤) = _
  rw [ConstantPullback.originalConstantSheafPullback_unit]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual constant inverse-image iso is adjoint to the original coefficient identity. -/
theorem originalAnalyticConstantInverseImageIso_homEquiv (f : X ⟶ Y) (A : AddCommGrpCat) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _
        ((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).hom.app A) =
      ConstantPullback.originalConstantSheafPullback f A := by
  apply ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    AddCommGrpCat isTerminalTop).homEquiv A _).injective
  rw [originalConstantSheafPullback_homEquiv]
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      AddCommGrpCat isTerminalTop).comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
          (DeRhamPresheafPullback.originalAnalyticSchemeMap f)))
    (constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat isTerminalTop) A
  rw [Adjunction.comp_homEquiv] at h
  exact h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantInverseImageNaturality
