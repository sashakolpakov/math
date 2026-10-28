import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffinePointCard
import Mathlib.FieldTheory.SeparableDegree

/-! # Field Point Count -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldPointCount.Construction

noncomputable section

/-! Geometric point counts of finite field extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The geometric points of the spectrum of an algebraic field extension
are counted by its separable degree. -/
theorem geometricPointCard_spec_field
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (s : Spec (.of K)) :
    Nat.card (DefinitionsTorsion.geometricPoint (Spec (.of K)) s ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) =
      Field.finSepDegree K L := by
  let C := AlgebraicClosure ((Spec (.of K)).residueField s)
  let t : Spec (.of C) ⟶ Spec (.of K) := (DefinitionsTorsion.geometricPoint (Spec (.of K)) s).hom
  let : Algebra K C := (Spec.preimage t).hom.toAlgebra
  have ht : Spec.map (CommRingCat.ofHom (algebraMap K C)) = t :=
    Spec.map_preimage t
  have he := AffinePointCard.Construction.specPointsEquivAlgHom K L C
  rw [ht] at he
  exact (Nat.card_congr he).trans (Field.finSepDegree_eq_of_isAlgClosed K L C).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldPointCount.Construction
