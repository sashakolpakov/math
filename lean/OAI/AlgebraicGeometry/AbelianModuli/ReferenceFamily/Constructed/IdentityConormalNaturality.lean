import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormalNaturality

/-! # Identity Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormalNaturality

noncomputable section

/-! The conormal constructed from the actual smooth group has natural
coefficient-valued lift coordinates, with the original coefficient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (C C' : Type) [CommRing C] [CommRing C'] [Algebra k C] [Algebra k C']
    (q : C →ₐ[k] C') (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})

def constructedIdentityRestrictedLift :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap q) ≫ c)} :=
  GroupLiftOpenCoordinates.groupLiftRestricted (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C')
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' q) (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap q))
    (Dual.CoefficientMapSquares.dualCoefficientOrigin_natural k C C' q) c f

variable [Smooth A.hom]

theorem constructedIdentityLiftConormalEquiv_natural (z : IdentityConormal.constructedIdentityConormal k A) :
    IdentityConormal.constructedIdentityLiftConormalEquiv k A C'
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap q) ≫ c)
      (constructedIdentityRestrictedLift k A C C' q c f) z =
      q (IdentityConormal.constructedIdentityLiftConormalEquiv k A C c f z) := by
  let B := IdentityConormal.constructedIdentityAlgebra k A
  let e : B →ₐ[k] k := IdentityConormal.constructedIdentityAugmentation k A
  let : Algebra B k := e.toRingHom.toAlgebra
  let : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  let : Algebra B C := ((algebraMap k C).comp e.toRingHom).toAlgebra
  let : Algebra B C' := ((algebraMap k C').comp e.toRingHom).toAlgebra
  let : IsScalarTower B k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower B k C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k C r = algebraMap k C (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let : IsScalarTower k B C' := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k C' r = algebraMap k C' (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let q₀ : C →ₐ[B] C' := {
    toRingHom := q.toRingHom
    commutes' b := by
      change q (algebraMap k C (e b)) = algebraMap k C' (e b)
      exact q.commutes (e b) }
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A := Affine.PointChartCoordinates.affinePointChartInclusion k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  have hopen : IsOpenImmersion i.left := Affine.PointChartCoordinates.affinePointChartInclusion_open k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1 :=
    Affine.PointChartCoordinates.affinePointChartAugmentation_fac k A 1 (IdentityConormal.selectedAffineIdentityChart k A)
  exact GroupCoefficientConormalNaturality.groupCoefficientConormalEquiv_natural k B C C' i hi q₀ c f z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormalNaturality
