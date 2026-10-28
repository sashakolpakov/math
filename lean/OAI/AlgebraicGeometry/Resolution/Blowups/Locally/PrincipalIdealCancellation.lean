import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Principal Ideal Cancellation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealCancellation.Construction

noncomputable section

/-! A nonzero locally principal factor cancels in equalities of actual native ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_idealSheaf_mul_left_injective
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (K : X.IdealSheafData) (hK : K ≠ ⊥) (hlocal : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf K) :
    Function.Injective (fun I : X.IdealSheafData => K * I) := by
  intro I J he
  choose W hx r hr hgen using PrincipalRegular.Construction.locallyPrincipal_regular_generators K hK hlocal
  let : ∀ x, IsOpenImmersion (W x).2.fromSpec := fun x => (W x).2.isOpenImmersion_fromSpec
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => Spec Γ(X, W x))
    (fun x => (W x).2.fromSpec) (by
      intro x
      refine ⟨x, ?_⟩
      change x ∈ (W x).2.fromSpec.opensRange
      rw [(W x).2.opensRange_fromSpec]
      exact hx x) (fun _ => inferInstance)
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover I J C
  intro x
  change X at x
  let : Nonempty (W x).1 := ⟨⟨x, hx x⟩⟩
  have h := congrArg (fun N : X.IdealSheafData => N.ideal (W x)) he
  change K.ideal (W x) * I.ideal (W x) = K.ideal (W x) * J.ideal (W x) at h
  rw [hgen x] at h
  have heq := Ideal.span_singleton_mul_right_injective
    (nonZeroDivisors.ne_zero (hr x).mem_nonZeroDivisors) h
  change I.comap (W x).2.fromSpec = J.comap (W x).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, heq]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealCancellation.Construction
