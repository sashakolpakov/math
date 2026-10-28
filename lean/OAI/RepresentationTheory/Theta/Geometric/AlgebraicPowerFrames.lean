import OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

/-! # Algebraic Power Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicPowerFrames

noncomputable section

/-! Frames of the actual HilbertConstruction tensor-power sheaf and their scalar law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def unitScalarEnd {X : Scheme.{u}} (r : Γ(X, ⊤)) : CategoryTheory.End (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r

theorem unitEndomorphism_pow {X : Scheme.{u}} (r : Γ(X, ⊤)) (n : ℕ) :
    unitScalarEnd r ^ n = unitScalarEnd (r ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection_one).symm
  | succ n hn =>
    rw [pow_succ']
    change (unitScalarEnd r ^ n) ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r = AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (r ^ (n + 1))
    rw [hn]
    exact (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection_comp (r ^ n) r).trans
      (congrArg AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (pow_succ r n).symm)

def tensorPowerGlobalFrame {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n

set_option backward.isDefEq.respectTransparency false in
theorem tensorPowerGlobalFrame_scalar {X : Scheme.{u}} {M : X.Modules}
    (e g : M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (r : Γ(X, ⊤))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) (n : ℕ) :
    (tensorPowerGlobalFrame e n).hom =
      (tensorPowerGlobalFrame g n).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (r ^ n) := by
  have hu := AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units.tensorPowerMap_unit_conjugation (unitScalarEnd r) n
  rw [unitEndomorphism_pow] at hu
  have hu' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) n ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (r ^ n) := by
    have hh := congrArg (fun t => (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom ≫ t) hu
    simpa only [unitScalarEnd, Iso.hom_inv_id_assoc] using hh
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap e.hom n ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom = _
  rw [h, AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_comp, Category.assoc, hu']
  rfl

def tensorPowerOpenFrame {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n).restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι M n).symm ≪≫ tensorPowerGlobalFrame e n

set_option backward.isDefEq.respectTransparency false in
theorem tensorPowerOpenFrame_scalar {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (r : Γ(U.toScheme, ⊤))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) (n : ℕ) :
    (tensorPowerOpenFrame M U e n).hom =
      (tensorPowerOpenFrame M U g n).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (r ^ n) := by
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι M n).inv ≫ (tensorPowerGlobalFrame e n).hom = _
  rw [tensorPowerGlobalFrame_scalar e g r h n]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicPowerFrames
