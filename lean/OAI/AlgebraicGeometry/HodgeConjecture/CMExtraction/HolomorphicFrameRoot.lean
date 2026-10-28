import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameRoot

/-! # Holomorphic Frame Root -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicFrameRoot

noncomputable section

/-! Holomorphy of the square root of the actual native frame determinant.
Continuity selects the local inverse of squaring at every nonzero value. -/

open scoped Classical _root_.Matrix

namespace Weil

theorem square_root_differentiableOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (O : Set X) (f g : X → ℂ) (hf : ContinuousOn f O) (hg : DifferentiableOn ℂ g O)
    (hsq : ∀ x ∈ O, f x ^ 2 = g x) (hne : ∀ x ∈ O, f x ≠ 0) :
    DifferentiableOn ℂ f O := by
  intro x hx
  have hd : HasStrictDerivAt (fun z : ℂ => z ^ 2) (2 * f x) (f x) := by
    simpa using hasStrictDerivAt_pow 2 (f x)
  have hd0 : 2 * f x ≠ 0 := mul_ne_zero (by norm_num) (hne x hx)
  let inv := hd.localInverse _ _ _ hd0
  have hi : DifferentiableAt ℂ inv (g x) := by
    rw [← hsq x hx]
    exact (hd.to_localInverse hd0).hasDerivAt.differentiableAt
  have hc : DifferentiableWithinAt ℂ (fun y => inv (g y)) O x :=
    hi.comp_differentiableWithinAt x (hg x hx)
  have he : (fun y => inv (g y)) =ᶠ[nhdsWithin x O] f := by
    have hlocal := hd.eventually_left_inverse hd0
    filter_upwards [(hf x hx) hlocal, self_mem_nhdsWithin] with y hy hyO
    rw [← hsq y hyO]
    exact hy
  exact hc.congr_of_eventuallyEq_of_mem he.symm hx

end Weil

namespace Multiplicity

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))

def nativeFrameRootExtension (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : ℂ :=
  if hz : z ∈ P.domain then Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he ⟨z, hz⟩
  else Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he (Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hP)

theorem nativeFrameRootExtension_on_domain (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    nativeFrameRootExtension E P hP hμ v hv e he z =
      Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he ⟨z, hz⟩ := by
  simp only [nativeFrameRootExtension, dite_eq_left hz]

theorem nativeFrameRootExtension_ne_zero (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    nativeFrameRootExtension E P hP hμ v hv e he z ≠ 0 := by
  unfold nativeFrameRootExtension
  split_ifs <;> exact Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he _

theorem nativeFrameRootExtension_continuousOn :
    ContinuousOn (nativeFrameRootExtension E P hP hμ v hv e he) P.domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he).continuous.congr
    (fun z => (nativeFrameRootExtension_on_domain E P hP hμ v hv e he z z.property).symm)

theorem nativeFrameRootExtension_differentiable :
    DifferentiableOn ℂ (nativeFrameRootExtension E P hP hμ v hv e he) P.domain := by
  apply Weil.square_root_differentiableOn P.domain _
    (fun z => (Multiplicity.Period.nativeLowerFrame E P hP v e z).det)
    (nativeFrameRootExtension_continuousOn E P hP hμ v hv e he)
  · apply PeriodMatrixFamilies.Multiplicity.matrix_family_det_differentiable
    apply PeriodFrameFamilies.Multiplicity.lowerFrame_differentiable
    intro z _
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  · intro z hz
    rw [nativeFrameRootExtension_on_domain E P hP hμ v hv e he z hz]
    exact Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot_sq E P hP hμ v hv e he ⟨z, hz⟩
  · intro z _
    exact nativeFrameRootExtension_ne_zero E P hP hμ v hv e he z

end Multiplicity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicFrameRoot
