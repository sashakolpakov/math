/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Stratification.Analytification
import OAI.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Analytification Is -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Complex points of the smooth decomposition

-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

/-- The inclusion of a reduced smooth stratum, bundled over the complex base. -/
def ComplexPoint.Basic.ComplexSchemePoint.reducedClosedSmoothPieceMap (T : Closeds X.left) :
    Over.mk (Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T ≫ X.hom) ⟶ X :=
  Over.homMk (Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T) rfl

instance ComplexPoint.Basic.ComplexSchemePoint.reducedClosedSmoothPieceMap_isImmersion (T : Closeds X.left) :
    IsImmersion (ComplexPoint.Basic.ComplexSchemePoint.reducedClosedSmoothPieceMap X T).left := by
  change IsImmersion (Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T)
  infer_instance

end

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

/-- Forgetting a complex point to its underlying Zariski point is continuous for the
analytic topology. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.continuous_underlying_to_zariski :
    Continuous (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint X → X.left) := by
  rw [continuous_def]
  exact fun S hS => ComplexPoint.Basic.Point.isOpen_overOpen ⟨S, hS⟩

/-- The complex points of a locally closed subscheme map onto exactly the complex points
whose underlying scheme point belongs to its range. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Set.range (ComplexPoint.Basic.Point.map i) =
      (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint X → X.left) ⁻¹' Set.range i.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.underlying, rfl⟩
  · rintro ⟨y, hy⟩
    have hyclosed : IsClosed ({y} : Set Y.left) := by
      have h := ((pointEquivClosedPoint X.hom) ⟨z.left, z.w⟩).2.preimage i.left.continuous
      change IsClosed (i.left ⁻¹' ({z.underlying} : Set X.left)) at h
      have he : i.left ⁻¹' ({z.underlying} : Set X.left) = {y} := by
        rw [← hy]
        ext a
        exact i.left.isEmbedding.injective.eq_iff
      rwa [he] at h
    let p := (pointEquivClosedPoint Y.hom).symm ⟨y, hyclosed⟩
    let w : ComplexPoint.Basic.ComplexSchemePoint Y := Over.homMk p.1 p.2
    refine ⟨w, ?_⟩
    apply Over.OverMorphism.ext
    have heq :
        (⟨(ComplexPoint.Basic.Point.map i w).left, (ComplexPoint.Basic.Point.map i w).w⟩ :
          {q : Spec ↧ℂ ⟶ X.left // q ≫ X.hom = 𝟙 _}) = ⟨z.left, z.w⟩ := by
      apply (pointEquivClosedPoint X.hom).injective
      apply Subtype.ext
      change i.left w.underlying = z.underlying
      have hw : w.underlying = y :=
        congrArg Subtype.val
          ((pointEquivClosedPoint Y.hom).apply_symm_apply ⟨y, hyclosed⟩)
      rw [hw]
      exact hy
    exact congrArg Subtype.val heq

end

end OAI.AlgebraicGeometry
