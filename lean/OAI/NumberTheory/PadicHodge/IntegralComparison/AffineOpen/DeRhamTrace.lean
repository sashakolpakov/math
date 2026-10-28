import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # De Rham Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace

noncomputable section

/-! The finite étale trace on the original sheaf de Rham sections over
an actual affine open where the coordinate algebra is free. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit.Intrinsic

universe u v w

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U : Y.left.Opens)

abbrev targetRing := IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y U
abbrev sourceRing := IntrinsicDeRham.SectionUnit.Intrinsic.ring R X (f.left ⁻¹ᵁ U)

@[instance_reducible]
def sectionAlgebra : Algebra (targetRing R Y U) (sourceRing R X Y f U) :=
  (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U).toRingHom.toAlgebra

local instance : Algebra (targetRing R Y U) (sourceRing R X Y f U) := sectionAlgebra R X Y f U

local instance sectionTower : IsScalarTower R (targetRing R Y U) (sourceRing R X Y f U) :=
  IsScalarTower.of_algebraMap_eq (fun r => ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U).commutes r).symm)

theorem sectionEtale (hU : IsAffineOpen U) :
    Algebra.Etale (targetRing R Y U) (sourceRing R X Y f U) := by
  change (f.left.app U).hom.Etale
  rw [Scheme.Hom.app_eq_appLE]
  exact f.left.etale_appLE hU (hU.preimage f.left) le_rfl

variable [Fact (IsAffineOpen U)]

local notation "hU" => (Fact.out : IsAffineOpen U)

variable (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (targetRing R Y U)]

local instance polynomialSource : Algebra (MvPolynomial σ R) (sourceRing R X Y f U) :=
  ((algebraMap (targetRing R Y U) (sourceRing R X Y f U)).comp
    (algebraMap (MvPolynomial σ R) (targetRing R Y U))).toAlgebra

local instance polynomialTower :
    IsScalarTower (MvPolynomial σ R) (targetRing R Y U) (sourceRing R X Y f U) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance polynomialBaseTower : IsScalarTower R (MvPolynomial σ R) (sourceRing R X Y f U) :=
  IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R (sourceRing R X Y f U) r =
      algebraMap (targetRing R Y U) (sourceRing R X Y f U)
        (algebraMap (MvPolynomial σ R) (targetRing R Y U) (algebraMap R (MvPolynomial σ R) r))
    rw [← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (targetRing R Y U)]
    exact ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U).commutes r).symm)

local instance sourceEtale : Algebra.Etale (MvPolynomial σ R) (sourceRing R X Y f U) := by
  let : Algebra.Etale (targetRing R Y U) (sourceRing R X Y f U) := sectionEtale R X Y f U hU
  exact Algebra.Etale.comp (MvPolynomial σ R) (targetRing R Y U) (sourceRing R X Y f U)

variable {ι : Type v} [Fintype ι] (b : Module.Basis ι (targetRing R Y U) (sourceRing R X Y f U))

def map : IntrinsicDeRham.SectionUnit.Intrinsic.sections R X (f.left ⁻¹ᵁ U) ⟶ IntrinsicDeRham.SectionUnit.Intrinsic.sections R Y U :=
  (IntrinsicDeRham.SectionUnit.Intrinsic.iso R X (f.left ⁻¹ᵁ U) ((Fact.out : IsAffineOpen U).preimage f.left) σ).inv ≫
    IntegralComparison.Etale.DeRhamTrace.trace R (targetRing R Y U) (sourceRing R X Y f U) σ b ≫
      (IntrinsicDeRham.SectionUnit.Intrinsic.iso R Y U hU σ).hom

theorem map_unit :
    IntrinsicDeRham.SectionUnit.Intrinsic.unit R X (f.left ⁻¹ᵁ U) ≫ map R X Y f U σ b =
      IntegralComparison.Etale.DeRhamTrace.trace R (targetRing R Y U) (sourceRing R X Y f U) σ b ≫
        IntrinsicDeRham.SectionUnit.Intrinsic.unit R Y U := by
  change (IntrinsicDeRham.SectionUnit.Intrinsic.iso R X (f.left ⁻¹ᵁ U) ((Fact.out : IsAffineOpen U).preimage f.left) σ).hom ≫ _ = _
  simp only [map, Iso.hom_inv_id_assoc]
  rfl

variable (τ : Type u) [Fintype τ] [LinearOrder τ]
  [Algebra (MvPolynomial τ R) (targetRing R Y U)]
  [IsScalarTower R (MvPolynomial τ R) (targetRing R Y U)]
  [Algebra.Etale (MvPolynomial τ R) (targetRing R Y U)]
  {κ : Type w} [Fintype κ]
  (c : Module.Basis κ (targetRing R Y U) (sourceRing R X Y f U))

theorem map_coordinate_independent : map R X Y f U σ b = map R X Y f U τ c := by
  have ht := IntegralComparison.Etale.DeRhamTraceCoordinates.trace_coordinate_independent R
    (targetRing R Y U) (sourceRing R X Y f U) σ b τ c
  unfold map
  rw [ht]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace
