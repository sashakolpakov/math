import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.OrderedLatticeLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeMap

/-! # Division Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DivisionNaturality

noncomputable section

/-! The canonical native division comparison commutes with original
algebraic group maps. It therefore retains the ordered torsion labels
as actual morphisms over the complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeMap.IntrinsicLinearMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper C.toOver.hom := C.variety.presentation.projective.isProper

def originalLatticeMap (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) :=
  LatticeMap.IntrinsicLinearMaps.nativeLatticeMap ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv)

theorem nativeDivisionEquiv_mk [NeZero N] (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    (OrderedLatticeLevel.nativeDivisionEquiv A PA (N := N) (QuotientAddGroup.mk v)).toMul.val =
      (Maps.IntrinsicAlgebraicMaps.periodAddEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) (TorsionCongruence.TorusTorsion.latticeDivisionPoint (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) N v).val).toMul ≫
        (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom := rfl

theorem nativeDivisionEquiv_natural [NeZero N]
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) N) :
    (OrderedLatticeLevel.nativeDivisionEquiv B PB (LatticeDivision.TorusTorsion.modNMap N (originalLatticeMap A B PA PB f).toAddMonoidHom x)).toMul.val =
      (OrderedLatticeLevel.nativeDivisionEquiv A PA x).toMul.val ≫ f := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [LatticeDivision.TorusTorsion.modNMap_mk, nativeDivisionEquiv_mk, nativeDivisionEquiv_mk]
  let CA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB
  let F := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv
  have hp := Maps.IntrinsicLinearMaps.linearLift_period F ((N : ℚ)⁻¹ • v.val)
  have hs := ((Maps.IntrinsicLinearMaps.linearLift F).restrictScalars ℚ).map_smul (N : ℚ)⁻¹ v.val
  change Maps.IntrinsicLinearMaps.linearLift F ((N : ℚ)⁻¹ • v.val) = (N : ℚ)⁻¹ • Maps.IntrinsicLinearMaps.linearLift F v.val at hs
  rw [hs] at hp
  have he := congrArg (fun p => p ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom) hp
  change ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv CA (TorsionCongruence.TorusTorsion.latticeDivisionPoint (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice CA) N v).val).toMul ≫
      ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv)) ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom =
    (Maps.IntrinsicAlgebraicMaps.periodAddEquiv CB (TorsionCongruence.TorusTorsion.latticeDivisionPoint (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice CB) N (originalLatticeMap A B PA PB f v)).val).toMul ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).hom at he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DivisionNaturality
