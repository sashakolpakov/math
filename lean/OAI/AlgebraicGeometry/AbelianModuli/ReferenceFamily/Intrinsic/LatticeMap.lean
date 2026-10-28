import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision

/-! # Lattice Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeMap.IntrinsicLinearMaps

noncomputable section

/-! Actual algebraic group morphisms induce integral lattice maps.
Their division points transform by the same native exponential map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f]

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper C.toOver.hom := C.variety.presentation.projective.isProper

def nativeLatticeMap : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B :=
  (((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℤ).domRestrict (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).codRestrict
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (fun v => Maps.IntrinsicLinearMaps.linearLift_preserves f v.val v.property)

theorem nativeLatticeMap_apply (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    (nativeLatticeMap f v).val = Maps.IntrinsicLinearMaps.linearLift f v.val := rfl

theorem nativeLatticeDivision_map (N : ℕ) [NeZero N] (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f (TorsionCongruence.TorusTorsion.latticeDivisionPoint (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) N v).val =
      (TorsionCongruence.TorusTorsion.latticeDivisionPoint (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) N (nativeLatticeMap f v)).val := by
  have h := Maps.IntrinsicLinearMaps.linearLift_lifts f ((N : ℚ)⁻¹ • v.val)
  exact h.trans (congrArg (fun w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B => (Maps.IntrinsicAlgebraicMaps.torus B).proj w)
    (((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ).map_smul (N : ℚ)⁻¹ v.val))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeMap.IntrinsicLinearMaps
