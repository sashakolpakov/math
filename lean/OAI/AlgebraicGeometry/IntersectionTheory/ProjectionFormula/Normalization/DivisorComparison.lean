import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Height

/-! # Divisor Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

noncomputable section

/-! The principal divisor on the global finite normalization pushes to the
original divisor at every codimension-one point. This assembles the actual
normalized-stalk formula using the complete normalization fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkMap
  StalkFields StalkFiber Affine.DivisorNorm CyclePushforward

universe u

variable {k : Type u} [Field k] [CharZero k]
  (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include f in
theorem normalization_noetherian : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.normalization X) := by
  let : IsFinite (Normalization.Scheme.normalizationMap X) := Normalization.Scheme.normalizationMap_isFinite X f
  let : IsLocallyNoetherian (Normalization.Scheme.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalization.Scheme.normalizationMap X ≫ f)
  let : CompactSpace (Normalization.Scheme.normalization X) :=
    QuasiCompact.compactSpace_of_compactSpace (Normalization.Scheme.normalizationMap X)
  exact {}

theorem normalizedPrincipalDivisor_comap
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)
    (hx : coheight (x : X) = 1) (g : X.functionField) :
    letI := normalization_noetherian X f
    letI := Support.Normalization.stalk_normalization_isDedekind f x hx
    Finsupp.comapDomain (StalkMap.normalizationStalkMap X U hU x)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Fields.normalizationFieldIso X).hom g))
      (StalkFiber.normalizationStalkMap_injective X U hU x).injOn =
        Affine.DivisorNorm.rationalPrincipalDivisor
          (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))
          (NormalizedStalkDivisor.normalizedStalkFunction f x hx g) := by
  let := normalization_noetherian X f
  let := Support.Normalization.stalk_normalization_isDedekind f x hx
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (StalkMap.normalizationStalkMap X U hU x)
      (StalkMap.normalizationStalkMap_genericPoint X U hU x)) :=
    inferInstanceAs (IsIso (StalkFields.stalkNormalizationFieldMap X U hU x))
  ext y
  let := StalkMap.normalizationStalkMap_stalkMap_isIso X U hU x y
  have h := Divisor.StalkIso.ord_eq_of_stalkMap_isIso (StalkMap.normalizationStalkMap X U hU x)
    (StalkMap.normalizationStalkMap_genericPoint X U hU x) y
    (StalkMap.normalizationStalkMap_coheight X U hU x y) ((Fields.normalizationFieldIso X).hom g)
  change (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))).ord
    (StalkFields.stalkNormalizationFieldMap X U hU x ((Fields.normalizationFieldIso X).hom g)) y = _ at h
  rw [StalkFields.normalizationFunction_restrict X U hU x f hx g] at h
  exact congrArg (fun n : ℤ => (n : ℚ)) h.symm

/-- At every divisor point, pushforward from the constructed global
normalization reproduces the original scheme's actual integer order. -/
theorem normalization_divisor_coefficient (x : X) (hx : coheight x = 1)
    (g : X.functionField) (hg : g ≠ 0) :
    letI := normalization_noetherian X f
    CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Fields.normalizationFieldIso X).hom g)) x =
        (X.ord g x : ℚ) := by
  let := normalization_noetherian X f
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let x' : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨x'⟩
  let := Support.Normalization.stalk_normalization_isDedekind f x hx
  rw [PushforwardFiber.pointPushforward_coeff_of_fiber_cover
    (StalkMap.normalizationStalkMap X U hU x') (Normalization.Scheme.normalizationMap X) x
    (StalkFiber.normalizationStalkMap_injective X U hU x')
    (StalkMap.normalizationStalkMap_residueDegree X U hU x')
    (StalkFiber.normalizationStalkMap_covers_fiber X U hU x'),
    normalizedPrincipalDivisor_comap X f U hU x' hx g,
    StalkMap.normalizationStalkMap_comp]
  rw [NormalizedStalkDivisor.normalizedStalk_pushforward_to_scheme f x hx g hg,
    Finsupp.single_eq_same]

/-- The actual finite principal divisor on the global normalization pushes
to the original principal divisor, including all its coefficients. -/
theorem normalization_principalDivisor (g : X.functionField) (hg : g ≠ 0) :
    letI := normalization_noetherian X f
    CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X)
      (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Fields.normalizationFieldIso X).hom g)) =
        Affine.DivisorNorm.rationalPrincipalDivisor X g := by
  let := normalization_noetherian X f
  ext x
  by_cases hx : coheight x = 1
  · exact normalization_divisor_coefficient X f x hx g hg
  · rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx, Int.cast_zero]
    apply PushforwardFiber.pointPushforward_apply_eq_zero
    intro y hy hxy
    have hyone : coheight y = 1 := by
      by_contra hn
      apply hy
      rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn,
        Int.cast_zero]
    apply hx
    rw [← hxy, Height.normalizationMap_coheight X f y, hyone]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison
