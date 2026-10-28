import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Residue Scalar Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueScalarIso

noncomputable section

/-! A local-ring isomorphism identifies residue modules with the correct restricted coefficient action. -/
open _root_.CategoryTheory IsLocalRing
universe u

def localResidueRestrictionIso
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : ModuleCat.of R (ResidueField R) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S (ResidueField S)) := by
  let eK := ResidueField.mapEquiv e
  let E : ResidueField R ≃ₗ[R]
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S (ResidueField S))) := {
    toFun := eK
    invFun := eK.symm
    left_inv := eK.left_inv
    right_inv := eK.right_inv
    map_add' := eK.map_add
    map_smul' := fun r x => by
      change eK (residue R r * x) = residue S (e r) * eK x
      rw [eK.map_mul]
      rfl }
  exact E.toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueScalarIso
