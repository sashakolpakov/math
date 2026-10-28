import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTensorPower
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafPowers

/-! # Unbundled Powers -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPowers

noncomputable section

/-! Tensor powers on the homogeneous Picard sheaf without a global
dimension parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
  (A : Over S) [GrpObj A]

theorem homogeneousPicardTensorPowerPresheaf_eq_pow :
    UnbundledTensorPower.Construction.UnbundledPicard.homogeneousPicardTensorPowerPresheaf p hp hS A =
      Functor.whiskerRight (SheafPowers.Construction.commGroupPresheafPow (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A) p)
        (forget CommGrpCat) := by
  ext T q
  apply Subtype.ext
  exact TensorPowerGroup.Construction.tensorPowerClass_eq_pow p q.val

theorem homogeneousPicardTensorPower_eq_pow (T : Over S)
    (q : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T)) :
    (UnbundledTensorPower.Construction.UnbundledPicard.homogeneousPicardTensorPower p hp hS A).hom.app (op T) q = q ^ p := by
  change (sheafifyMap (Scheme.fppfTopology.over S)
    (UnbundledTensorPower.Construction.UnbundledPicard.homogeneousPicardTensorPowerPresheaf p hp hS A)).app (op T) q = q ^ p
  rw [homogeneousPicardTensorPowerPresheaf_eq_pow]
  exact SheafPowers.Construction.picardTypeSheafify_pow (UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A) p (op T) q

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPowers
