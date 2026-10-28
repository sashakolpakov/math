import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MapConstantReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftReduction

/-! # Dual Constant Lift Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualConstantLiftPullback

noncomputable section

/-! An actual affine lift of a fixed base-valued point pulls back
identically through a deformed dual coefficient map and through its
ordinary coefficient map. This equality retains the original scheme lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C D : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing D]
    [Algebra k B] [Algebra k C] [Algebra k D] [Algebra B C] [IsScalarTower k B C]
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C]
    (q : C →ₐ[k] D) (f : DualNumber C →ₐ[k] DualNumber D)
    (hred : ∀ u, (f u).fst = q u.fst) (heps : f DualNumber.eps = DualNumber.eps)

include hred heps

omit [IsScalarTower k B k] in
theorem affineDualConstantLift_deformed
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)}) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) f ≫ u.val =
      AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) (Dual.NumberCoefficients.dualNumberAlgMap q) ≫ u.val := by
  let a := OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B u.val
  have ha (b : B) : (a b).fst = algebraMap k C (algebraMap B k b) := by
    have hu := AlgHom.congr_fun
      ((DualLiftReduction.affineDualLift_reduction_iff k B C (IsScalarTower.toAlgHom k B C) u.val).mp u.property) b
    exact hu.trans (IsScalarTower.algebraMap_apply B k C b)
  have H : f.comp a = (Dual.NumberCoefficients.dualNumberAlgMap q).comp a :=
    AlgHom.ext (fun b => Dual.MapConstantReduction.dualMap_constantReduction q f hred heps (a b) (algebraMap B k b) (ha b))
  rw [← OverMorphismAlgebra.affineOverMorphismAlgebra_recovery k (DualNumber C) B u.val,
    OverMorphismAlgebra.affineOverAlgHom_comp, OverMorphismAlgebra.affineOverAlgHom_comp]
  exact congrArg (AlgebraAutomorphismNaturality.affineOverAlgHom k B (DualNumber D)) H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualConstantLiftPullback
