import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalSmoothLocalization

/-! # Local Parameter Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterCoordinates.Constructions

noncomputable section

/-!
# DegreeTwo: actual normal coordinates on a smooth principal neighborhood

Only a principal open of the divisor need be smooth. Localization and the
genuine open embedding of affine points return normal coordinates on the
original ambient affine space, preserving its original parameter.
-/

open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Local smoothness of the actual principal quotient suffices for normal
coordinates on the original ambient point space. -/
theorem exists_local_parameter_normal_coordinates (p b : S) (hp : p ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) (hxb : x b ≠ 0) :
    ∃ (g : Localization.Away b) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m))
      (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away b))
        (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (q : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
        (ℂ × (fderiv ℂ (fun z => e.symm z (algebraMap S (Localization.Away b) p))
          (e (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x b hxb))).ker)),
      x ∈ q.source ∧ q x = 0 ∧
      q.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b ∧
      (∀ y ∈ q.source, (q y).1 = y p) ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => q.symm z a) q.target) := by
  let T := Localization.Away b
  have hb : b ≠ 0 := fun h => hxb (h ▸ map_zero x)
  let : IsDomain T := Localization.Away.isDomain hb
  let : Algebra.Smooth ℂ T := Algebra.Smooth.comp ℂ S T
  let p' := algebraMap S T p
  have hp' : p' ≠ 0 := (map_ne_zero_iff _ (IsLocalization.injective T
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb))).mpr hp
  let : Algebra.Smooth ℂ (T ⧸ Ideal.span {p'}) := PrincipalSmoothLocalization.Constructions.principal_quotient_localization_smooth ℂ S p b
  let y := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x b hxb
  have hyp : y p' = 0 := (DFunLike.congr_fun (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x b hxb) p).trans hxp
  obtain ⟨g, n, m, P, e, q, hyq, hqy, hq, hi⟩ := ParameterCoordinates.Constructions.exists_parameter_normal_coordinates p' hp' y hyp
  let ιb := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction b
  have hιb : Topology.IsOpenEmbedding ιb := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction b
  let r := q.lift_openEmbedding hιb
  have hιy : ιb y = x := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x b hxb
  refine ⟨g, n, m, P, e, r, ⟨y, hyq, hιy⟩, ?_, ?_, ?_, ?_⟩
  · change (q.lift_openEmbedding hιb) x = 0
    rw [← hιy, OpenPartialHomeomorph.lift_openEmbedding_apply, hqy]
  · rintro z ⟨w, _, rfl⟩
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph b w).property
  · rintro z ⟨w, hw, rfl⟩
    change ((q.lift_openEmbedding hιb) (ιb w)).1 = w p'
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact hq w hw
  · intro a
    exact hi (algebraMap S T a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterCoordinates.Constructions
