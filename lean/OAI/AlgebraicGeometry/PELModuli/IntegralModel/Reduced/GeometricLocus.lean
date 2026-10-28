import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ImmersionFactorization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Geometric Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.GeometricLocus

noncomputable section

/-! A locally closed locus classifies its geometric-point condition on
all reduced test schemes, with no noetherian restriction on the tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem reduced_immersion_lift_iff_geometric_points
    {X Y Z : Scheme.{0}} (i : X ⟶ Z) [IsImmersion i] (f : Y ⟶ Z) [IsReduced Y] :
    (∃! g : Y ⟶ X, g ≫ i = f) ↔
      ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Spec (.of F) ⟶ Y),
        ∃ q : Spec (.of F) ⟶ X, q ≫ i = p ≫ f := by
  constructor
  · rintro ⟨g, hg, _⟩ F _ _ p
    exact ⟨p ≫ g, (Category.assoc _ _ _).trans (congrArg (p ≫ ·) hg)⟩
  · intro h
    apply ImmersionFactorization.existsUnique_lift_immersion_of_range_subset i f
    rintro _ ⟨y, rfl⟩
    let F := AlgebraicClosure (Y.residueField y)
    let p : Spec (.of F) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) F)) ≫ Y.fromSpecResidueField y
    have hp : p (IsLocalRing.closedPoint F) = y := Y.fromSpecResidueField_apply y _
    obtain ⟨q, hq⟩ := h F p
    refine ⟨q (IsLocalRing.closedPoint F), ?_⟩
    have he := congrArg (fun m => m (IsLocalRing.closedPoint F)) hq
    exact he.trans (congrArg f hp)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.GeometricLocus
