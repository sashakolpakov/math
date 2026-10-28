import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalkFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.NormFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationNorm

/-! # Normalization Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationDivisor

noncomputable section

/-! Global norm-divisor pushforward for finite relative normalization over
a base with DVR local rings at codimension one. All local branches are
included by the actual stalk-spectrum fiber cover. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationCharts
  NormalizationStalks NormalizationStalkFields
  Affine.DivisorNorm CyclePushforward

attribute [local instance] NormalizationStalks.sectionAlgebra NormalizationStalks.stalkAlgebra

universe u

variable {k : Type u} [Field k] [CharZero k]
  (Y : Scheme.{u}) [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y]
  (L : Type u) [Field L] [Algebra Y.functionField L] [Module.Finite Y.functionField L]
  (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include f in
theorem relativeNormalization_noetherian : AlgebraicGeometry.IsNoetherian (Normalization.relativeNormalization Y L) := by
  let : IsFinite (Normalization.relativeNormalizationMap Y L) := Normalization.relativeNormalizationMap_isFinite Y L f
  let : IsLocallyNoetherian (Normalization.relativeNormalization Y L) :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalization.relativeNormalizationMap Y L ≫ f)
  let : CompactSpace (Normalization.relativeNormalization Y L) :=
    QuasiCompact.compactSpace_of_compactSpace (Normalization.relativeNormalizationMap Y L)
  exact {}

/-- The coefficient at each base divisor point is the order of the norm
of the original rational function, in the chosen extension coordinates. -/
theorem principalDivisor_coefficient (y : Y) (hy : coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (g : (Normalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    CyclePushforward.pointPushforward (Normalization.relativeNormalizationMap Y L)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.relativeNormalization Y L) g) y =
        (Y.ord (Algebra.norm Y.functionField ((NormalizationFields.relativeFunctionFieldIso Y L).hom g)) y : ℚ) := by
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
  let ψ := NormalizationStalkFields.stalkFieldMap Y L U hU y'
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalks.stalkMap Y L U hU y')
      (NormalizationStalks.stalkMap_genericPoint Y L U hU y')) :=
    inferInstanceAs (IsIso (NormalizationStalkFields.stalkFieldMap Y L U hU y'))
  have hcomap : Finsupp.comapDomain (NormalizationStalks.stalkMap Y L U hU y')
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.relativeNormalization Y L) g)
      (NormalizationStalks.stalkMap_injective Y L U hU y').injOn =
        Affine.DivisorNorm.rationalPrincipalDivisor (Spec (.of D)) (ψ g) := by
    ext z
    let := NormalizationStalks.stalkMap_stalkMap_isIso Y L U hU y' z
    have h := Divisor.StalkIso.ord_eq_of_stalkMap_isIso (NormalizationStalks.stalkMap Y L U hU y')
      (NormalizationStalks.stalkMap_genericPoint Y L U hU y') z (NormalizationStalks.stalkMap_coheight Y L U hU y' z) g
    exact congrArg (fun n : ℤ => (n : ℚ)) h.symm
  have hψ : ψ g ≠ 0 := (map_ne_zero_iff ψ.hom ψ.hom.injective).mpr hg
  have hlocal := Affine.NormFields.principalDivisor_pushforward R D Y.functionField L (ψ g) hψ
  have hfield : (Affine.FractionField.fieldIso D L).hom (ψ g) =
      (NormalizationFields.relativeFunctionFieldIso Y L).hom g :=
    congrArg (fun t : (Normalization.relativeNormalization Y L).functionField ⟶ CommRingCat.of L => t g)
      (NormalizationStalkFields.stalkFieldMap_square Y L U hU y')
  rw [hfield] at hlocal
  have hclosed : Y.fromSpecStalk y' (IsLocalRing.closedPoint R) = y :=
    Scheme.fromSpecStalk_closedPoint
  rw [PushforwardFiber.pointPushforward_coeff_of_fiber_cover
    (NormalizationStalks.stalkMap Y L U hU y') (Normalization.relativeNormalizationMap Y L) y
    (NormalizationStalks.stalkMap_injective Y L U hU y') (NormalizationStalks.stalkMap_residueDegree Y L U hU y')
    (NormalizationStalks.stalkMap_covers_fiber Y L U hU y'), hcomap, NormalizationStalks.stalkMap_comp,
    CyclePushforward.pointPushforward_comp, LinearMap.comp_apply, hlocal, CyclePushforward.pointPushforward_single,
    Stalk.ResidueDegree.fromSpecStalk_residueDegree, Nat.cast_one, mul_one]
  let c : ℚ := (WithZero.log
    (Ring.ordFrac R (Algebra.norm Y.functionField ((NormalizationFields.relativeFunctionFieldIso Y L).hom g))) : ℤ)
  trans c
  · exact (congrArg (fun z : Y => (Finsupp.single z c) y) hclosed).trans Finsupp.single_eq_same
  · rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
    rfl

/-- The finite relative normalization pushes a principal divisor to the
principal divisor of its norm. -/
theorem principalDivisor_norm
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : (Normalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    CyclePushforward.pointPushforward (Normalization.relativeNormalizationMap Y L)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.relativeNormalization Y L) g) =
        Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField ((NormalizationFields.relativeFunctionFieldIso Y L).hom g)) := by
  let := relativeNormalization_noetherian Y L f
  ext y
  by_cases hy : coheight y = 1
  · let := hDVR y hy
    exact principalDivisor_coefficient Y L f y hy g hg
  · rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hy, Int.cast_zero]
    apply PushforwardFiber.pointPushforward_apply_eq_zero
    intro z hz hzy
    have hzone : coheight z = 1 := by
      by_contra hn
      apply hz
      rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn, Int.cast_zero]
    apply hy
    rw [← hzy, NormalizationCharts.relativeNormalizationMap_coheight Y L f z, hzone]

/-- The same identity entirely in native scheme function fields, using
the norm of the actual generic-stalk embedding. -/
theorem principalDivisor_native_norm
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : (Normalization.relativeNormalization Y L).functionField) (hg : g ≠ 0) :
    letI := relativeNormalization_noetherian Y L f
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L)
      (NormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
    CyclePushforward.pointPushforward (Normalization.relativeNormalizationMap Y L)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.relativeNormalization Y L) g) =
        Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField g) := by
  let := relativeNormalization_noetherian Y L f
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L)
    (NormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
  rw [NormalizationNorm.relativeFieldMap_norm Y L]
  exact principalDivisor_norm Y L f hDVR g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationDivisor
