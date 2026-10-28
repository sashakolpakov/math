import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationStalkFields
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecifiedNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationNorm

/-! # Normalization Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationDivisor.BundleCycles.RelativeNormalizationDivisor

noncomputable section

/-! Global norm-divisor pushforward for finite relative normalization over
a base with DVR local rings at codimension one. All local branches are
included by the actual stalk-spectrum fiber cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationCharts.BundleCycles.RelativeNormalizationCharts
  NormalizationStalks.BundleCycles.RelativeNormalizationStalks NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields
  IntersectionTheory.ProjectionFormula.CyclePushforward

attribute [local instance] NormalizationStalks.BundleCycles.RelativeNormalizationStalks.sectionAlgebra NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkAlgebra

variable {k : Type} [Field k] [CharZero k]
  (Y : Scheme.{0}) [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y]
  (L : Type) [Field L] [Algebra Y.functionField L] [Module.Finite Y.functionField L]
  (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include f in
theorem relativeNormalization_noetherian : AlgebraicGeometry.IsNoetherian (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) := by
  let : IsFinite (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) := Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap_isFinite Y L f
  let : IsLocallyNoetherian (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ≫ f)
  let : CompactSpace (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) :=
    QuasiCompact.compactSpace_of_compactSpace (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
  exact {}

/-- The coefficient at each base divisor point is the order of the norm
of the original rational function, in the chosen extension coordinates. -/
theorem principalDivisor_coefficient (y : Y) (hy : coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (g : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) g) y =
        (Y.ord (Algebra.norm Y.functionField ((NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom g)) y : ℚ) := by
  let := relativeNormalization_noetherian Y L f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let : CharZero Y.functionField := charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  let R := Y.presheaf.stalk y
  let D := integralClosure R L
  let : CharZero R := (algebraMap R Y.functionField).charZero
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R Y.functionField L
  let : Module.IsTorsionFree R D := IsIntegralClosure.isTorsionFree R L
  let : IsDedekindDomain D := integralClosure.isDedekindDomain R Y.functionField L
  let : Module.Finite R D := IsIntegralClosure.finite R Y.functionField L D
  let : IsFractionRing D L := integralClosure.isFractionRing_of_finite_extension Y.functionField L
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  let y' : U := ⟨y, hyU⟩
  let : Nonempty U := ⟨y'⟩
  let ψ := NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields.stalkFieldMap Y L U hU y'
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y')
      (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_genericPoint Y L U hU y')) :=
    inferInstanceAs (IsIso (NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields.stalkFieldMap Y L U hU y'))
  have hcomap : Finsupp.comapDomain (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y')
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) g)
      (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_injective Y L U hU y').injOn =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of D)) (ψ g) := by
    ext z
    let := NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_stalkMap_isIso Y L U hU y' z
    have h := MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y')
      (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_genericPoint Y L U hU y') z (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_coheight Y L U hU y' z) g
    exact congrArg (fun n : ℤ => (n : ℚ)) h.symm
  have hψ : ψ g ≠ 0 := (map_ne_zero_iff ψ.hom ψ.hom.injective).mpr hg
  have hlocal := Affine.SpecifiedNorm.BundleCycles.affineSpecifiedNormPrincipalDivisor_pushforward R D Y.functionField L (ψ g) hψ
  have hfield : (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).hom (ψ g) =
      (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom g :=
    congrArg (fun t : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField ⟶ CommRingCat.of L => t g)
      (NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields.stalkFieldMap_square Y L U hU y')
  rw [hfield] at hlocal
  have hclosed : Y.fromSpecStalk y' (IsLocalRing.closedPoint R) = y :=
    Scheme.fromSpecStalk_closedPoint
  rw [IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_coeff_of_fiber_cover
    (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y') (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) y
    (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_injective Y L U hU y') (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_residueDegree Y L U hU y')
    (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_covers_fiber Y L U hU y'), hcomap, NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_comp,
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply, hlocal]
  let c : ℚ := (WithZero.log
    (Ring.ordFrac R (Algebra.norm Y.functionField ((NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom g))) : ℤ)
  let z : Spec (Y.presheaf.stalk y) := IsLocalRing.closedPoint (Y.presheaf.stalk y)
  have hz : (Y.fromSpecStalk y).residueDegree z = 1 :=
    IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree.fromSpecStalk_residueDegree Y y
  have hzy : Y.fromSpecStalk y z = y := Scheme.fromSpecStalk_closedPoint
  have hp := congrArg (fun q : Y →₀ ℚ => q y)
    (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single (Y.fromSpecStalk y) z c)
  rw [hz, Nat.cast_one, mul_one, hzy, Finsupp.single_eq_same] at hp
  apply hp.trans
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  rfl

/-- The finite relative normalization pushes a principal divisor to the
principal divisor of its norm. -/
theorem principalDivisor_norm
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) g) =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField ((NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom g)) := by
  let := relativeNormalization_noetherian Y L f
  ext y
  by_cases hy : coheight y = 1
  · let := hDVR y hy
    exact principalDivisor_coefficient Y L f y hy g hg
  · rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hy, Int.cast_zero]
    apply IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_apply_eq_zero
    intro z hz hzy
    have hzone : coheight z = 1 := by
      by_contra hn
      apply hz
      rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn, Int.cast_zero]
    apply hy
    rw [← hzy, NormalizationCharts.BundleCycles.RelativeNormalizationCharts.relativeNormalizationMap_coheight Y L f z, hzone]

/-- The same identity entirely in native scheme function fields, using
the norm of the actual generic-stalk embedding. -/
theorem principalDivisor_native_norm
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) g) =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
  let := relativeNormalization_noetherian Y L f
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
  rw [NormalizationNorm.BundleCycles.RelativeNormalizationNorm.relativeFieldMap_norm Y L]
  exact principalDivisor_norm Y L f hDVR g hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationDivisor.BundleCycles.RelativeNormalizationDivisor
