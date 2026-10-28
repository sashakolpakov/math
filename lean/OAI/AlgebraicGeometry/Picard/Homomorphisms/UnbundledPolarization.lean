import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualFrobenius
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPowers

/-! # Unbundled Polarization -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPolarization

noncomputable section

/-! The Frobenius polarization pullback formula over an arbitrary base,
without a constant relative dimension. The multiplication on the dual
is the one represented by actual tensor products of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

theorem dualPicardTensorPower_eq_groupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    letI := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower p hp hS D = (𝟙 D.abelian) ^ p := by
  let := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  apply (UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D D.abelian).injective
  rw [map_pow, UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv_apply, UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv_apply]
  change D.representable.homEquiv
      (D.representable.homEquiv.symm
        ((UnbundledTensorPower.Construction.UnbundledPicard.homogeneousPicardTensorPower p hp hS A).hom.app (op D.abelian)
          (D.representable.homEquiv (𝟙 D.abelian)))) = _
  rw [Equiv.apply_symm_apply]
  exact UnbundledPowers.Construction.UnbundledPicard.homogeneousPicardTensorPower_eq_pow p hp hS A D.abelian _

variable (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem frobenius_dual_picardGroupPow :
    letI := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian ≫ UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS =
      (𝟙 D.abelian) ^ p :=
  (UnbundledDualFrobenius.Construction.UnbundledPicard.frobenius_dual_eq_picardTensorPower D p hp hS).trans
    (dualPicardTensorPower_eq_groupPow D p hp hS)

/-- The polarization pullback formula holds for every map to the Picard-derived dual,
and therefore in particular for a map arising from an ample line bundle. -/
theorem frobenius_pullback_picardGroupPow (ell : A ⟶ D.abelian) :
    letI := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Frobenius.Construction.relativeFrobenius p hp hS A ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS = ell ^ p := by
  let := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  calc
    _ = ell ≫ UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower p hp hS D := UnbundledDualFrobenius.Construction.UnbundledPicard.frobenius_pullback_dualMap D p hp hS ell
    _ = ell ≫ (𝟙 D.abelian) ^ p :=
      congrArg (fun z => ell ≫ z) (dualPicardTensorPower_eq_groupPow D p hp hS)
    _ = ell ^ p := by rw [MonObj.comp_pow, Category.comp_id]

/-- The same equality in the usual additive notation for maps into the dual. -/
theorem frobenius_pullback_picardGroup_nsmul (ell : A ⟶ D.abelian) :
    letI := UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Additive.ofMul (Frobenius.Construction.relativeFrobenius p hp hS A ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS) = p • Additive.ofMul ell :=
  congrArg Additive.ofMul (frobenius_pullback_picardGroupPow D p hp hS ell)

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPolarization
