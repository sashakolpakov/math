import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PointChartCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalMaps

/-! # Identity Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal

noncomputable section

/-! A smooth group over a field supplies its actual affine identity
neighborhood and finite conormal space. Arbitrary-coefficient group lifts
then have coordinates in the coefficient dual of this constructed space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A]

def selectedAffineIdentityChart : Affine.RationalPointChart.AffineOverPointChart k A (1 : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ A) :=
  Classical.choice (Affine.RationalPointChart.exists_affineOverPointChart k A (1 : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ A))

abbrev constructedIdentityAlgebra : CommAlgCat k :=
  Affine.PointChartCoordinates.affinePointChartAlgebra k A 1 (selectedAffineIdentityChart k A)

def constructedIdentityAugmentation : constructedIdentityAlgebra k A →ₐ[k] k :=
  Affine.PointChartCoordinates.affinePointChartAugmentation k A 1 (selectedAffineIdentityChart k A)

abbrev constructedIdentityConormal := PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module (constructedIdentityAugmentation k A)

instance constructedIdentityAlgebra_smooth [Smooth A.hom] : Algebra.Smooth k (constructedIdentityAlgebra k A) :=
  Affine.PointChartCoordinates.affinePointChartAlgebra_smooth k A 1 (selectedAffineIdentityChart k A)

instance constructedIdentityConormal_finite [Smooth A.hom] : Module.Finite k (constructedIdentityConormal k A) :=
  (PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.finite_projective (constructedIdentityAugmentation k A)).1

variable [Smooth A.hom] (C : Type) [CommRing C] [Algebra k C]

def constructedIdentityLiftConormalEquiv (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c} ≃
      (constructedIdentityConormal k A →ₗ[k] C) := by
  let B := constructedIdentityAlgebra k A
  let e : B →ₐ[k] k := constructedIdentityAugmentation k A
  let : Algebra B k := e.toRingHom.toAlgebra
  let : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  let : Algebra B C := ((algebraMap k C).comp e.toRingHom).toAlgebra
  let : IsScalarTower B k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k C r = algebraMap k C (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A := Affine.PointChartCoordinates.affinePointChartInclusion k A 1 (selectedAffineIdentityChart k A)
  have hopen : IsOpenImmersion i.left :=
    Affine.PointChartCoordinates.affinePointChartInclusion_open k A 1 (selectedAffineIdentityChart k A)
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1 :=
    Affine.PointChartCoordinates.affinePointChartAugmentation_fac k A 1 (selectedAffineIdentityChart k A)
  exact GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
