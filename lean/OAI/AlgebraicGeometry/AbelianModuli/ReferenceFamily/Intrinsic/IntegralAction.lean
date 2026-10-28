import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction

noncomputable section

/-! An actual integral PEL endomorphism action induces ring actions on
the native complex period space and on its genuine integral lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps

variable {R : Type*} [CommRing R] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) (ρ : ActionData.IntegralAction R A)

def nativeMap (a : R) : (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver ⟶ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver :=
  (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ ρ.map a ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv

instance nativeMap_isMonHom (a : R) : IsMonHom (nativeMap A P ρ a) :=
  inferInstanceAs (IsMonHom ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ ρ.map a ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv))

theorem nativeMap_zero : nativeMap A P ρ 0 = 1 := by
  simp only [nativeMap, ρ.map_zero, MonObj.one_comp, MonObj.comp_one]

theorem nativeMap_one : nativeMap A P ρ 1 = 𝟙 _ := by
  simp only [nativeMap, ρ.map_one, Category.id_comp, Iso.hom_inv_id]

theorem nativeMap_add (a b : R) : nativeMap A P ρ (a + b) =
    nativeMap A P ρ a * nativeMap A P ρ b := by
  simp only [nativeMap, ρ.map_add, MonObj.mul_comp, MonObj.comp_mul]

theorem nativeMap_mul (a b : R) : nativeMap A P ρ (a * b) =
    nativeMap A P ρ b ≫ nativeMap A P ρ a := by
  simp only [nativeMap, ρ.map_mul, Category.assoc, Iso.inv_hom_id_assoc]

/-- The complex-linear action is derived from the unique native lifts
of the actual algebraic endomorphisms. -/
def linearAction : R →+* Module.End ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) where
  toFun a := Maps.IntrinsicLinearMaps.linearLift (nativeMap A P ρ a)
  map_zero' := (Maps.IntrinsicLinearMaps.linearLift_congr _ _ (nativeMap_zero A P ρ)).trans (Maps.IntrinsicLinearMaps.linearLift_zero _ _)
  map_one' := (Maps.IntrinsicLinearMaps.linearLift_congr _ _ (nativeMap_one A P ρ)).trans (Maps.IntrinsicLinearMaps.linearLift_id _)
  map_add' a b := (Maps.IntrinsicLinearMaps.linearLift_congr _ _ (nativeMap_add A P ρ a b)).trans (Maps.IntrinsicLinearMaps.linearLift_add _ _)
  map_mul' a b := (Maps.IntrinsicLinearMaps.linearLift_congr _ _ (nativeMap_mul A P ρ a b)).trans (Maps.IntrinsicLinearMaps.linearLift_comp _ _)

theorem linearAction_preserves (a : R) (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
    (hv : v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) : linearAction A P ρ a v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) :=
  Maps.IntrinsicLinearMaps.linearLift_preserves (nativeMap A P ρ a) v hv

/-- The same action restricts to the actual integral period lattice. -/
def latticeAction : R →+* Module.End ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) where
  toFun a := (((linearAction A P ρ a).restrictScalars ℤ).domRestrict
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))).codRestrict (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
      (fun v => linearAction_preserves A P ρ a v.val v.property)
  map_zero' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (linearAction A P ρ).map_zero v.val
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (linearAction A P ρ).map_one v.val
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun ((linearAction A P ρ).map_add a b) v.val
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun ((linearAction A P ρ).map_mul a b) v.val

theorem latticeAction_coe (a : R) (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    (latticeAction A P ρ a v).val = linearAction A P ρ a v.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction
