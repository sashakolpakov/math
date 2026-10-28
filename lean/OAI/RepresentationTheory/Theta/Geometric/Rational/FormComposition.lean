import OAI.RepresentationTheory.Theta.Geometric.Rational.FormsPullback
import OAI.RepresentationTheory.Theta.Geometric.Rational.ContravariantExtension

/-! # Form Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Actual rational pullbacks preserve identities, reverse composition,
and turn algebraic units into invertible operators on algebraic forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

local instance Data.ActiveHeckeThetaData.rationalComposition_addGroup : AddCommGroup D.pel.OneFormsA :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_mul (a b : D.pel.EndQ) :
    D.rationalFormsPullback hg (a * b) =
      (D.rationalFormsPullback hg b).comp (D.rationalFormsPullback hg a) := by
  exact Rational.ContravariantExtension.rationalExtensionOfAddHom_mul_reverse
    (A := D.pel.EndK) (B := Module.End ℂ D.pel.OneFormsA)
    (D.integralFormsPullbackAddHom hg) D.pel.pullbackForms_mul a b

theorem Data.ActiveHeckeThetaData.rationalFormsPullback_one : D.rationalFormsPullback hg 1 = 1 := by
  apply Rational.ContravariantExtension.rationalExtensionOfAddHom_one
    (A := D.pel.EndK) (B := Module.End ℂ D.pel.OneFormsA)
    (D.integralFormsPullbackAddHom hg)
  change D.pel.pullbackForms 1 = 1
  unfold AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.pullbackForms
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_one, CategoryTheory.Functor.map_id, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_id]
  rfl

def Data.ActiveHeckeThetaData.rationalUnitForms (u : D.pel.EndQˣ) : (Module.End ℂ D.pel.OneFormsA)ˣ where
  val := D.rationalFormsPullback hg u.val
  inv := D.rationalFormsPullback hg (↑u⁻¹ : D.pel.EndQ)
  val_inv := (D.rationalFormsPullback_mul hg (↑u⁻¹ : D.pel.EndQ) u.val).symm.trans
    (by rw [Units.inv_mul, D.rationalFormsPullback_one])
  inv_val := (D.rationalFormsPullback_mul hg u.val (↑u⁻¹ : D.pel.EndQ)).symm.trans
    (by rw [Units.mul_inv, D.rationalFormsPullback_one])

theorem Data.ActiveHeckeThetaData.heckeRationalForms_one (A : TateComparison.Action D.pel) : D.heckeRationalForms hg A 1 = 1 := by
  change D.rationalFormsPullback hg (A.algebraAction 1) = 1
  rw [map_one, D.rationalFormsPullback_one]

theorem Data.ActiveHeckeThetaData.heckeRationalForms_mul (A : TateComparison.Action D.pel) (h k : SphericalGU.Spherical.FullHecke q s) :
    D.heckeRationalForms hg A (h * k) =
      (D.heckeRationalForms hg A k).comp (D.heckeRationalForms hg A h) := by
  change D.rationalFormsPullback hg (A.algebraAction (h * k)) = _
  rw [map_mul, D.rationalFormsPullback_mul]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
