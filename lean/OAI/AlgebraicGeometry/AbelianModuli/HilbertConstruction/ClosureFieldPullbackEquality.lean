import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Closure Field Pullback Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosureFieldPullbackEquality

noncomputable section

/-! Equality on algebraically closed field pullbacks implies equality on
all field pullbacks, by faithfully flat extension to an algebraic closure. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X Y : Over S} (f q : X ⟶ Y)

theorem overHom_fieldPullbacks_eq_of_algClosed
    (h : ∀ (F : Type u) [Field F] [IsAlgClosed F] (x : Spec (.of F) ⟶ S),
      (Over.pullback x).map f = (Over.pullback x).map q)
    (K : Type u) [Field K] (x : Spec (.of K) ⟶ S) :
    (Over.pullback x).map f = (Over.pullback x).map q := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let : Flat (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  let : Surjective (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  apply (Over.pullback (Spec.map φ)).map_injective
  exact (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated (Spec.map φ) x f q).mp
    (h (AlgebraicClosure K) (Spec.map φ ≫ x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosureFieldPullbackEquality
