import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PointGroups
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Geometric Configuration -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The ordered full-level labels determine distinct actual geometric
points of the abelian scheme, all killed by multiplication by the level.
For nonzero level their cardinality is exactly n^(2g). -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] {g n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel n)

def Abelian.Schemes.AbelianScheme.fullLevelGeometricPoint (c : Multiplicative (Fin (2 * g) → ZMod n)) : A.scheme.left :=
  ((A.fullLevelRationalTorsionEquiv level).symm c).val.left (IsLocalRing.closedPoint K)

theorem Abelian.Schemes.AbelianScheme.fullLevelGeometricPoint_injective [IsAlgClosed K] : Function.Injective (A.fullLevelGeometricPoint level) := by
  intro a b hab
  apply (A.fullLevelRationalTorsionEquiv level).symm.injective
  apply Subtype.ext
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq A.scheme.hom
    ((A.fullLevelRationalTorsionEquiv level).symm a).val.w
    ((A.fullLevelRationalTorsionEquiv level).symm b).val.w hab

theorem Abelian.Schemes.AbelianScheme.fullLevelGeometricPoint_multiplication (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    (A.multiplication n).left (A.fullLevelGeometricPoint level c) =
      η[A.scheme].left (IsLocalRing.closedPoint K) := by
  let x := (A.fullLevelRationalTorsionEquiv level).symm c
  have h := (A.torsion_condition_iff n (Over.mk (𝟙 (Spec (.of K)))) x.val).mpr x.property
  have hp := congrArg (fun f : Spec (.of K) ⟶ A.scheme.left => f (IsLocalRing.closedPoint K)) h
  simpa only [Scheme.Hom.comp_apply] using! hp

theorem Abelian.Schemes.AbelianScheme.fullLevelGeometricPoint_label_card [NeZero n] :
    Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) = n ^ (2 * g) := by
  simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
