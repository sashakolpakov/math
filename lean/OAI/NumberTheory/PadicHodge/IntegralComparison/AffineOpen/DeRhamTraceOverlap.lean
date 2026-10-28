import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction

/-! # De Rham Trace Overlap -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceOverlap

noncomputable section

/-! Actual affine traces commute with restriction even when the two
affine opens use different polynomial étale charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction

universe u v w

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U V : Y.left.Opens)
  [Fact (IsAffineOpen U)] [Fact (IsAffineOpen V)] [Fact (V ≤ U)]

local instance : Algebra (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) := DeRhamTrace.sectionAlgebra R X Y f U
local instance : Algebra (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) := DeRhamTrace.sectionAlgebra R X Y f V

variable (σ τ : Type u) [Fintype σ] [LinearOrder σ] [Fintype τ] [LinearOrder τ]
  [Algebra (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [Algebra (MvPolynomial τ R) (DeRhamTrace.targetRing R Y V)]
  [IsScalarTower R (MvPolynomial τ R) (DeRhamTrace.targetRing R Y V)]
  [Algebra.Etale (MvPolynomial τ R) (DeRhamTrace.targetRing R Y V)]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U))
  (c : Module.Basis κ (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V))

theorem map_restriction :
    DeRhamTrace.map R X Y f U σ b ≫ IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restriction R Y (DeRhamTraceRestriction.targetInclusion R Y U V) =
      IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restriction R X (DeRhamTraceRestriction.sourceInclusion R X Y f U V) ≫
        DeRhamTrace.map R X Y f V τ c := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R Y (DeRhamTraceRestriction.targetInclusion R Y U V)
  let : IsScalarTower R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) :=
    IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R Y (DeRhamTraceRestriction.targetInclusion R Y U V)
  let : Algebra (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) :=
    ((algebraMap (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)).comp
      (algebraMap (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U))).toAlgebra
  let : IsScalarTower (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap R (DeRhamTrace.targetRing R Y V) r =
        algebraMap (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)
          (algebraMap (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (algebraMap R (MvPolynomial σ R) r))
      rw [← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
      exact (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map (DeRhamTraceRestriction.targetInclusion R Y U V).op).hom.commutes r).symm)
  let : Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) :=
    DeRhamTraceRestriction.smallerEtale R Y U V σ
  have h := DeRhamTraceRestriction.map_restriction R X Y f U V σ b c
  rw [DeRhamTrace.map_coordinate_independent R X Y f V σ c τ c] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceOverlap
