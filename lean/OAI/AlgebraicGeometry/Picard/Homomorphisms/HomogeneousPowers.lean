import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousTensorPower
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafPowers

/-! # Homogeneous Powers -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPowers

noncomputable section

/-! Tensor powers are group powers in the homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem homogeneousPicardTensorPowerPresheaf_eq_pow :
    HomogeneousTensorPower.Construction.homogeneousPicardTensorPowerPresheaf p hp hS A =
      Functor.whiskerRight (SheafPowers.Construction.commGroupPresheafPow (HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A) p)
        (forget CommGrpCat) := by
  ext T q
  apply Subtype.ext
  exact TensorPowerGroup.Construction.tensorPowerClass_eq_pow p q.val

theorem homogeneousPicardTensorPower_eq_pow (T : Over S)
    (q : A.homogeneousPicardSheaf.obj.obj (op T)) :
    (HomogeneousTensorPower.Construction.homogeneousPicardTensorPower p hp hS A).hom.app (op T) q = q ^ p := by
  change (sheafifyMap (Scheme.fppfTopology.over S)
    (HomogeneousTensorPower.Construction.homogeneousPicardTensorPowerPresheaf p hp hS A)).app (op T) q = q ^ p
  rw [homogeneousPicardTensorPowerPresheaf_eq_pow]
  exact SheafPowers.Construction.picardTypeSheafify_pow (HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A) p (op T) q

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPowers
