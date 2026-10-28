import Mathlib

/-! # Correspondences -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences

noncomputable section

/-!
Actual algebraic correspondences and their composition by fiber products.
The chain/fiber equivalence is constructed from the pullback universal
property. Neither pointwise convolution nor an Albanese action is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A correspondence finite etale over its source, defined over the given base. -/
structure EtaleCorrespondence {B : Scheme.{u}} (X : Over B) where
  cover : Over B
  source : cover ⟶ X
  target : cover ⟶ X
  finite : IsFinite source.left
  etale : Etale source.left

attribute [instance] EtaleCorrespondence.finite EtaleCorrespondence.etale

namespace EtaleCorrespondence

variable {B : Scheme.{u}} {X : Over B}

/-- Composition is the actual scheme-theoretic fiber product. -/
abbrev comp (C D : EtaleCorrespondence X) : EtaleCorrespondence X where
  cover := pullback C.target D.source
  source := pullback.fst C.target D.source ≫ C.source
  target := pullback.snd C.target D.source ≫ D.target
  finite := by
    change IsFinite ((pullback.fst C.target D.source).left ≫ C.source.left)
    have : IsFinite (pullback.fst C.target D.source).left := by
      exact MorphismProperty.of_isPullback (P := @IsFinite)
        ((Over.forget B).map_isPullback
          (IsPullback.of_hasPullback C.target D.source)).flip D.finite
    infer_instance
  etale := by
    change Etale ((pullback.fst C.target D.source).left ≫ C.source.left)
    have : Etale (pullback.fst C.target D.source).left := by
      exact MorphismProperty.of_isPullback (P := @Etale)
        ((Over.forget B).map_isPullback
          (IsPullback.of_hasPullback C.target D.source)).flip D.etale
    infer_instance

/-- A geometric branch retains its source-fiber point, including multiplicity. -/
abbrev Fiber (C : EtaleCorrespondence X) {T : Over B} (x : T ⟶ X) :=
  {c : T ⟶ C.cover // c ≫ C.source = x}

/-- The branch target is induced by the actual target morphism. -/
abbrev endpoint (C : EtaleCorrespondence X) {T : Over B} {x : T ⟶ X}
    (c : C.Fiber x) : T ⟶ X := c.val ≫ C.target

/-- Composable branches are an explicit dependent pair of geometric points. -/
abbrev Chain (C D : EtaleCorrespondence X) {T : Over B} (x : T ⟶ X) :=
  Σ c : C.Fiber x, D.Fiber (C.endpoint c)

/-- Every branch of the composed cover corresponds to exactly one chain. -/
def compFiberEquiv (C D : EtaleCorrespondence X) {T : Over B} (x : T ⟶ X) :
    (C.comp D).Fiber x ≃ C.Chain D x where
  toFun z :=
    ⟨⟨z.val ≫ pullback.fst C.target D.source, by
        simpa only [Category.assoc] using z.property⟩,
      ⟨z.val ≫ pullback.snd C.target D.source, by
        dsimp [EtaleCorrespondence.endpoint]
        rw [Category.assoc, Category.assoc, pullback.condition]⟩⟩
  invFun z :=
    ⟨pullback.lift z.1.val z.2.val z.2.property.symm, by
      dsimp [EtaleCorrespondence.comp]
      rw [← Category.assoc, pullback.lift_fst, z.1.property]⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv z := by
    rcases z with ⟨c, d⟩
    dsimp
    have hc :
        (⟨pullback.lift c.val d.val d.property.symm ≫ pullback.fst C.target D.source,
          (congrArg (fun k => k ≫ C.source)
            (pullback.lift_fst c.val d.val d.property.symm)).trans c.property⟩ :
          C.Fiber x) = c := by
      apply Subtype.ext
      exact pullback.lift_fst _ _ _
    apply Sigma.ext hc
    apply (Subtype.heq_iff_coe_eq (fun y => by
      change (y ≫ D.source =
        (pullback.lift c.val d.val d.property.symm ≫ pullback.fst C.target D.source) ≫
          C.target) ↔ y ≫ D.source = c.val ≫ C.target
      rw [pullback.lift_fst])).mpr
    exact pullback.lift_snd _ _ _

/-- The equivalence preserves the final moduli point, not just cardinality. -/
theorem compFiberEquiv_endpoint (C D : EtaleCorrespondence X)
    {T : Over B} (x : T ⟶ X) (z : (C.comp D).Fiber x) :
    D.endpoint (C.compFiberEquiv D x z).2 = (C.comp D).endpoint z := by
  dsimp [EtaleCorrespondence.compFiberEquiv, EtaleCorrespondence.endpoint, EtaleCorrespondence.comp]
  exact Category.assoc _ _ _

end EtaleCorrespondence

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences
