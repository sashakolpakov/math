import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.ProperCoherentExt
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing

/-! # Affine Coherent Ext -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineCoherentExt.FlatBaseAffineCoherentExt

noncomputable section

/-! # Positive original coefficient Ext vanishes for quasicoherent modules on affine schemes -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
  (M : X.left.Modules) [M.IsQuasicoherent]

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem subsingleton (n : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (ProperCoherentExt.FlatBaseProperCoherentExt.sheaf R X M) (n + 1)) := by
  let : Subsingleton (SheafCohomology.AffineH.Projective.H M (n + 1)) := SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton M n
  exact (ProperCoherentExt.FlatBaseProperCoherentExt.addEquiv R X M (n + 1)).injective.subsingleton

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineCoherentExt.FlatBaseAffineCoherentExt
