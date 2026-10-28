import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualFrobenius

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarization

noncomputable section

/-! Frobenius pullback is multiplication by p for the dual constructed from Picard groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem frobenius_dual_picardGroupPow :
    letI := CanonicalDualGroup.Construction.dualPicardGroup D
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ≫ DualFrobenius.Construction.dualRelativeFrobenius D p hp hS =
      (𝟙 D.abelian.scheme) ^ p :=
  (DualFrobenius.Construction.frobenius_dual_eq_picardTensorPower D p hp hS).trans
    (CanonicalDualGroup.Construction.dualPicardTensorPower_eq_groupPow D p hp hS)

/-- The polarization pullback formula holds for every map to the Picard-derived dual,
and therefore in particular for a map arising from an ample line bundle. -/
theorem frobenius_pullback_picardGroupPow (ell : A.scheme ⟶ D.abelian.scheme) :
    letI := CanonicalDualGroup.Construction.dualPicardGroup D
    Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        DualFrobenius.Construction.dualRelativeFrobenius D p hp hS = ell ^ p := by
  let := CanonicalDualGroup.Construction.dualPicardGroup D
  calc
    _ = ell ≫ HomogeneousTensorPower.Construction.dualPicardTensorPower p hp hS D := DualFrobenius.Construction.frobenius_pullback_dualMap D p hp hS ell
    _ = ell ≫ (𝟙 D.abelian.scheme) ^ p :=
      congrArg (fun z => ell ≫ z) (CanonicalDualGroup.Construction.dualPicardTensorPower_eq_groupPow D p hp hS)
    _ = ell ^ p := by rw [MonObj.comp_pow, Category.comp_id]

/-- The same equality in the usual additive notation for maps into the dual. -/
theorem frobenius_pullback_picardGroup_nsmul (ell : A.scheme ⟶ D.abelian.scheme) :
    letI := CanonicalDualGroup.Construction.dualPicardGroup D
    Additive.ofMul (Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        DualFrobenius.Construction.dualRelativeFrobenius D p hp hS) = p • Additive.ofMul ell :=
  congrArg Additive.ofMul (frobenius_pullback_picardGroupPow D p hp hS ell)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarization
