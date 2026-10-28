import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedDivisorFiber
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Height
import OAI.AlgebraicGeometry.CycleClass.Thom.PushforwardFiber

/-! # Pushforward -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Pushforward.Constructions.Local

noncomputable section

/-!
# ThomClass: actual principal divisors push forward from finite normalization

The proof uses the entire normalization fiber, with canonical residue
field degrees and the actual pullback of rational functions. It applies
to singular integral supports and includes poles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- At every divisor point, pushforward from the constructed global
normalization reproduces the original scheme's actual integer order. -/
theorem normalizationPrincipalDivisor_coefficient (x : X) (hx : coheight x = 1)
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Normalization.Field.Constructions.finiteNormalization_noetherian X f
    Point.Constructions.pointPushforward (Normalization.Scheme.Constructions.normalizationMap X)
      (Point.Constructions.rationalPrincipalPointDivisor (Normalization.Scheme.Constructions.normalization X) ((Normalization.Fields.Constructions.normalizationFieldIso X).hom g)) x =
        (X.ord g x : ℚ) := by
  let := Normalization.Field.Constructions.finiteNormalization_noetherian X f
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let x' : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨x'⟩
  let := SupportNormalization.Constructions.stalk_normalization_isDedekind f x hx
  rw [PushforwardFiber.Constructions.pointPushforward_coeff_of_fiber_cover
    (Normalization.StalkMap.Constructions.Local.normalizationStalkMap X U hU x') (Normalization.Scheme.Constructions.normalizationMap X) x
    (Normalization.StalkMap.Constructions.Local.normalizationStalkMap_injective X U hU x')
    (Normalization.Fiber.Constructions.Local.normalizationStalkMap_residueDegree X U hU x')
    (Normalization.Fiber.Constructions.Local.normalizationStalkMap_covers_fiber X U hU x'),
    NormalizedDivisorFiber.Constructions.NormalizationLocal.normalizedPrincipalPointDivisor_comap X f U hU x' hx g,
    Normalization.StalkMap.Constructions.Local.normalizationStalkMap_comp]
  rw [NormalizedDivisorFiber.Constructions.NormalizationLocal.normalizedLocal_principalDivisor_toScheme X f x hx g hg,
    Finsupp.single_eq_same]

/-- The actual finite principal divisor on the global normalization pushes
to the original principal divisor, including all its coefficients. -/
theorem normalizationPrincipalDivisor_pushforward (g : X.functionField) (hg : g ≠ 0) :
    letI := Normalization.Field.Constructions.finiteNormalization_noetherian X f
    Point.Constructions.pointPushforward (Normalization.Scheme.Constructions.normalizationMap X)
      (Point.Constructions.rationalPrincipalPointDivisor (Normalization.Scheme.Constructions.normalization X) ((Normalization.Fields.Constructions.normalizationFieldIso X).hom g)) =
        Point.Constructions.rationalPrincipalPointDivisor X g := by
  let := Normalization.Field.Constructions.finiteNormalization_noetherian X f
  ext x
  by_cases hx : coheight x = 1
  · exact normalizationPrincipalDivisor_coefficient X f x hx g hg
  · rw [Point.Constructions.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx, Int.cast_zero]
    apply PushforwardFiber.Constructions.pointPushforward_apply_eq_zero
    intro y hy hxy
    have hyone : coheight y = 1 := by
      by_contra hn
      apply hy
      rw [Point.Constructions.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn,
        Int.cast_zero]
    apply hx
    rw [← hxy, Normalization.Height.Constructions.Local.normalizationMap_coheight X f y, hyone]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Pushforward.Constructions.Local
