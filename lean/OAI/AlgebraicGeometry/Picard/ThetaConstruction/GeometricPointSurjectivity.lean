import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Lean.Util.CollectAxioms

/-! # Geometric Point Surjectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricPointSurjectivity.Geometric

noncomputable section

/-! Lifting every actual algebraically closed field point proves
surjectivity on the original scheme point spaces. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem surjective_of_geometricPoint_lifts {X Y : Scheme.{0}} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Y),
      ∃ p : Spec (.of K) ⟶ X, p ≫ f = t) : Surjective f := by
  constructor
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  let b := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  let t := b ≫ Y.fromSpecResidueField y
  obtain ⟨p, hp⟩ := h K t
  refine ⟨p (IsLocalRing.closedPoint K), ?_⟩
  exact (congrArg (fun q : Spec (.of K) ⟶ Y => q (IsLocalRing.closedPoint K)) hp).trans
    (Y.fromSpecResidueField_apply y (b (IsLocalRing.closedPoint K)))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GeometricPointSurjectivity.Geometric
