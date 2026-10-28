import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalRatioCoordinates

/-! # Conormal Ratio -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalRatio

noncomputable section

/-! The original constructed conormal records the quotient of a
lift by its reference. Translating an identity lift by any reference
therefore leaves these coordinates unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (C : Type) [CommRing C] [Algebra k C]

theorem constructedIdentityLiftConormalEquiv_eq_of_ratio
    (c c' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})
    (g : {g : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ g = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c'})
    (h : f.val / c = g.val / c') :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A C c f = IdentityConormal.constructedIdentityLiftConormalEquiv k A C c' g := by
  let B := IdentityConormal.constructedIdentityAlgebra k A
  let e := IdentityConormal.constructedIdentityAugmentation k A
  let : Algebra B k := e.toRingHom.toAlgebra
  let : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  let : Algebra B C := ((algebraMap k C).comp e.toRingHom).toAlgebra
  let : IsScalarTower B k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k C r = algebraMap k C (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A := Affine.PointChartCoordinates.affinePointChartInclusion k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  have : IsOpenImmersion i.left := Affine.PointChartCoordinates.affinePointChartInclusion_open k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1 :=
    Affine.PointChartCoordinates.affinePointChartAugmentation_fac k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  exact ConormalRatioCoordinates.groupCoefficientConormalEquiv_eq_of_ratio k B C i hi c c' f g h

def constructedConormalTranslatedLift (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ (1 : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)}) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c} :=
  ⟨f.val * c, by rw [MonObj.comp_mul, f.property, MonObj.comp_one, one_mul]⟩

theorem constructedIdentityLiftConormalEquiv_translate (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ (1 : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)}) :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A C c (constructedConormalTranslatedLift k A C c f) =
      IdentityConormal.constructedIdentityLiftConormalEquiv k A C 1 f :=
  constructedIdentityLiftConormalEquiv_eq_of_ratio k A C c 1 _ f
    ((mul_div_cancel_right f.val c).trans (div_one f.val).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalRatio
