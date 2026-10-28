import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualConstantLiftPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualMapReductionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal

/-! # Constructed Conormal Deformed Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstructedConormalDeformedNaturality

noncomputable section

section

/-! Translating an actual group lift to the identity removes the
extra term of a deformed coefficient map. Its conormal coordinates
therefore pull back by the original reduced coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C D : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing D]
    [Algebra k B] [Algebra k C] [Algebra k D] [Algebra B C] [Algebra B D]
    [IsScalarTower k B C] [IsScalarTower k B D]
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [IsScalarTower B k D]
    {A : Over (Spec (.of k))} [GrpObj A]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1)
    (q : C →ₐ[B] D) (m : DualNumber C →ₐ[k] DualNumber D)
    (hred : ∀ u, (m u).fst = q u.fst)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})

def groupCoefficientDeformedLift :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber D) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ u =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)} :=
  GroupLiftOpenCoordinates.groupLiftRestricted (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) (Dual.CoefficientSchemeTests.dualCoefficientOrigin k D)
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C D (q.restrictScalars k))
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m)
    (Affine.DualMapReductionSquare.affineDualMap_reduction_square k C D (q.restrictScalars k) m hred) c u

theorem groupCoefficientOpenLiftEquiv_deformed :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫
        (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c u).val =
      (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B D i hi
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
        (groupCoefficientDeformedLift k B C D q m hred c u)).val := by
  have : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  have hu : (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c u).val ≫ i = u.val / c :=
    GroupLiftOpenCoordinates.groupLiftOpenEquiv_fac (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)) (GroupCoefficientConormal.affineGroupIdentity_coefficients k B C i hi) c u
  have hv : (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B D i hi
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
        (groupCoefficientDeformedLift k B C D q m hred c u)).val ≫ i =
      (groupCoefficientDeformedLift k B C D q m hred c u).val /
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c) :=
    GroupLiftOpenCoordinates.groupLiftOpenEquiv_fac (Dual.CoefficientSchemeTests.dualCoefficientOrigin k D) i
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D)) (GroupCoefficientConormal.affineGroupIdentity_coefficients k B D i hi)
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
      (groupCoefficientDeformedLift k B C D q m hred c u)
  rw [Category.assoc, hu, hv, GrpObj.comp_div]
  rfl

variable [Algebra.FormallySmooth k B]

theorem groupCoefficientConormalEquiv_deformed_natural
    (heps : m DualNumber.eps = DualNumber.eps) (z : (RingHom.ker (algebraMap B k)).Cotangent) :
    GroupCoefficientConormal.groupCoefficientConormalEquiv k B D i hi
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
        (groupCoefficientDeformedLift k B C D q m hred c u) z =
      q (GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c u z) := by
  have H := Affine.DualConstantLiftPullback.affineDualConstantLift_deformed k B C D (q.restrictScalars k) m hred heps
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c u)
  exact Affine.DualLiftConormalNaturality.affineDualLiftConormalEquiv_natural k B C D q
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B C i hi c u)
    (GroupCoefficientConormal.groupCoefficientOpenLiftEquiv k B D i hi
      (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
      (groupCoefficientDeformedLift k B C D q m hred c u))
    (H.symm.trans (groupCoefficientOpenLiftEquiv_deformed k B C D i hi q m hred c u)) z

end

/-! The constructed native identity conormal coordinates commute
with actual maps of dual-number tests that preserve the base parameter.
Only their original reduced coefficient maps act on these coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (k : Type) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (C D : Type) [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
    (q : C →ₐ[k] D) (m : DualNumber C →ₐ[k] DualNumber D)
    (hred : ∀ u, (m u).fst = q u.fst)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})

def constructedIdentityDeformedLift :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber D) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ u =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k D ≫ (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)} :=
  GroupLiftOpenCoordinates.groupLiftRestricted (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) (Dual.CoefficientSchemeTests.dualCoefficientOrigin k D)
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C D q) (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m)
    (Affine.DualMapReductionSquare.affineDualMap_reduction_square k C D q m hred) c u

variable [Smooth A.hom]

theorem constructedIdentityLiftConormalEquiv_deformed_natural
    (heps : m DualNumber.eps = DualNumber.eps) (z : Constructed.IdentityConormal.constructedIdentityConormal k A) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A D
        (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber D) m ≫ c)
        (constructedIdentityDeformedLift k A C D q m hred c u) z =
      q (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A C c u z) := by
  let B := Constructed.IdentityConormal.constructedIdentityAlgebra k A
  let e : B →ₐ[k] k := Constructed.IdentityConormal.constructedIdentityAugmentation k A
  let : Algebra B k := e.toRingHom.toAlgebra
  let : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  let : Algebra B C := ((algebraMap k C).comp e.toRingHom).toAlgebra
  let : Algebra B D := ((algebraMap k D).comp e.toRingHom).toAlgebra
  let : IsScalarTower B k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower B k D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k C r = algebraMap k C (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let : IsScalarTower k B D := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k D r = algebraMap k D (e (algebraMap k B r))
    rw [e.commutes]
    rfl)
  let q₀ : C →ₐ[B] D := {
    toRingHom := q.toRingHom
    commutes' b := by
      change q (algebraMap k C (e b)) = algebraMap k D (e b)
      exact q.commutes (e b) }
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A := Affine.PointChartCoordinates.affinePointChartInclusion k A 1 (Constructed.IdentityConormal.selectedAffineIdentityChart k A)
  have : IsOpenImmersion i.left := Affine.PointChartCoordinates.affinePointChartInclusion_open k A 1 (Constructed.IdentityConormal.selectedAffineIdentityChart k A)
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1 :=
    Affine.PointChartCoordinates.affinePointChartAugmentation_fac k A 1 (Constructed.IdentityConormal.selectedAffineIdentityChart k A)
  exact groupCoefficientConormalEquiv_deformed_natural k B C D i hi q₀ m hred c u heps z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstructedConormalDeformedNaturality
