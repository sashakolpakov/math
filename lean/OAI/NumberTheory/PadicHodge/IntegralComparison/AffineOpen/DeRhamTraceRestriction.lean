import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.AffineRestrictionSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceBaseChange

/-! # De Rham Trace Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction

noncomputable section

/-! Restriction compatibility of the actual finite étale de Rham trace
on nested affine opens. The chart on the smaller open is inherited from
the larger open; coordinate independence allows any other chart there. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace

universe u v w

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U V : Y.left.Opens)
  [Fact (IsAffineOpen U)] [Fact (IsAffineOpen V)] [Fact (V ≤ U)]

abbrev targetInclusion : V ⟶ U := homOfLE (Fact.out : V ≤ U)

abbrev sourceInclusion : f.left ⁻¹ᵁ V ⟶ f.left ⁻¹ᵁ U :=
  (Opens.map f.left.base).map (targetInclusion R Y U V)

local instance targetAlgebra : Algebra (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) :=
  IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R Y (targetInclusion R Y U V)

local instance sourceAlgebra : Algebra (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V) :=
  IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X (sourceInclusion R X Y f U V)

local instance topAlgebra : Algebra (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.sectionAlgebra R X Y f U

local instance bottomAlgebra : Algebra (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.sectionAlgebra R X Y f V

local instance (priority := 100) diagonalAlgebra : Algebra (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f V) :=
  ((algebraMap (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V)).comp
    (algebraMap (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U))).toAlgebra

local instance topTower : IsScalarTower R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.sectionTower R X Y f U

local instance bottomTower : IsScalarTower R (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.sectionTower R X Y f V

local instance targetTower : IsScalarTower R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) :=
  IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R Y (targetInclusion R Y U V)

local instance sourceTower : IsScalarTower R (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V) :=
  IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionTower R X (sourceInclusion R X Y f U V)

local instance firstDiagonalTower :
    IsScalarTower (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance secondDiagonalTower :
    IsScalarTower (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    exact (ConcreteCategory.congr_hom
      (f.left.naturality (targetInclusion R Y U V).op) a).symm)

local instance sectionPushout :
    Algebra.IsPushout (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)
      (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V) := by
  apply CommRingCat.isPushout_iff_isPushout.mp
  exact Finite.AffineRestrictionSquare.isPushout f.left
    (Fact.out : V ≤ U) (Fact.out : IsAffineOpen U) (Fact.out : IsAffineOpen V)

variable (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]

variable [Algebra (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V)]
  [IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V)]
  [IsScalarTower (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)]

include U in
omit [Fintype σ] [LinearOrder σ] [IsScalarTower R (MvPolynomial σ R) ↑(DeRhamTrace.targetRing R Y U)] [IsScalarTower R (MvPolynomial σ R) ↑(DeRhamTrace.targetRing R Y V)] in
theorem smallerEtale : Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) := by
  let : Algebra.Etale (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V) :=
    IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R Y (targetInclusion R Y U V)
      (Fact.out : IsAffineOpen U) (Fact.out : IsAffineOpen V)
  exact Algebra.Etale.comp (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)

variable [Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V)]

local instance topPolynomialAlgebra : Algebra (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.polynomialSource R X Y f U σ

local instance bottomPolynomialAlgebra : Algebra (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.polynomialSource R X Y f V σ

local instance topPolynomialTower :
    IsScalarTower (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.polynomialTower R X Y f U σ

local instance bottomPolynomialTower :
    IsScalarTower (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.polynomialTower R X Y f V σ

local instance topPolynomialBaseTower : IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.polynomialBaseTower R X Y f U σ

local instance bottomPolynomialBaseTower : IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.polynomialBaseTower R X Y f V σ

local instance topEtale : Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f U) :=
  DeRhamTrace.sourceEtale R X Y f U σ

local instance bottomEtale : Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f V) :=
  DeRhamTrace.sourceEtale R X Y f V σ

local instance sourcePolynomialTower :
    IsScalarTower (MvPolynomial σ R) (DeRhamTrace.sourceRing R X Y f U) (DeRhamTrace.sourceRing R X Y f V) :=
  IsScalarTower.of_algebraMap_eq (fun p => by
    change algebraMap (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V)
      (algebraMap (MvPolynomial σ R) (DeRhamTrace.targetRing R Y V) p) = _
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) (DeRhamTrace.targetRing R Y V)]
    exact ConcreteCategory.congr_hom
      (f.left.naturality (targetInclusion R Y U V).op)
      (algebraMap (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U) p))

variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U))
  (c : Module.Basis κ (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V))

theorem map_restriction :
    DeRhamTrace.map R X Y f U σ b ≫ IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restriction R Y (targetInclusion R Y U V) =
      IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restriction R X (sourceInclusion R X Y f U V) ≫
        DeRhamTrace.map R X Y f V σ c := by
  let : IsIso (IntrinsicDeRham.SectionUnit.Intrinsic.unit R X (f.left ⁻¹ᵁ U)) :=
    IntrinsicDeRham.SectionUnit.Intrinsic.unit_isIso R X (f.left ⁻¹ᵁ U) ((Fact.out : IsAffineOpen U).preimage f.left) σ
  apply (cancel_epi (IntrinsicDeRham.SectionUnit.Intrinsic.unit R X (f.left ⁻¹ᵁ U))).mp
  have hn := IntegralComparison.Etale.DeRhamTraceBaseChange.trace_baseChange R
    (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U)
    (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) σ b c
  change IntegralComparison.Etale.DeRhamTrace.trace R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) σ b ≫
      IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction R Y (targetInclusion R Y U V) =
    IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction R X (sourceInclusion R X Y f U V) ≫
      IntegralComparison.Etale.DeRhamTrace.trace R (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) σ c at hn
  calc
    _ = (IntegralComparison.Etale.DeRhamTrace.trace R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) σ b ≫
        IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction R Y (targetInclusion R Y U V)) ≫ IntrinsicDeRham.SectionUnit.Intrinsic.unit R Y V := by
      rw [← Category.assoc, DeRhamTrace.map_unit, Category.assoc, IntrinsicDeRham.SectionRestriction.IntrinsicUnit.unit_restriction, ← Category.assoc]
    _ = (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction R X (sourceInclusion R X Y f U V) ≫
        IntegralComparison.Etale.DeRhamTrace.trace R (DeRhamTrace.targetRing R Y V) (DeRhamTrace.sourceRing R X Y f V) σ c) ≫
          IntrinsicDeRham.SectionUnit.Intrinsic.unit R Y V := by rw [hn]
    _ = _ := by
      rw [Category.assoc, ← DeRhamTrace.map_unit, ← Category.assoc, ← IntrinsicDeRham.SectionRestriction.IntrinsicUnit.unit_restriction, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceRestriction
