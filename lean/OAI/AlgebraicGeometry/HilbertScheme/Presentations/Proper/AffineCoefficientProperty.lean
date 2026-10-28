import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SourceCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.CompletionNoetherian
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientStrictness

/-! # Affine Coefficient Property -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineCoefficientProperty

noncomputable section

/-! The proper-source coefficient property, and its passage from strict
quotients to a principal completion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def ProperAffineCoefficientProperty (R : CommRingCat.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ Spec R) [Flat f] [IsProper f]
    (K : X.IdealSheafData), ∃ I : Ideal R, Affine.IdealCoefficientTests.IsAffineIdealCoefficient R f K I

theorem properAffineCoefficientProperty_principalCompletion
    (R : CommRingCat.{u}) [IsNoetherianRing R] (s : R) (hs : ¬ IsNilpotent s)
    (hquot : ∀ (A : CommRingCat.{u}) (φ : R ⟶ A), Function.Surjective φ →
      RingHom.ker φ.hom ≠ ⊥ → ProperAffineCoefficientProperty A) :
    ProperAffineCoefficientProperty (CommRingCat.of (AdicCompletion (Ideal.span {s}) R)) := by
  let I : Ideal R := Ideal.span {s}
  let H := CommRingCat.of (AdicCompletion I R)
  let J : Ideal H := I.map (algebraMap R H)
  let : IsNoetherianRing H := Principal.CompletionNoetherian.principal_completion_isNoetherian R s
  let : IsAdicComplete J H :=
    (IsAdicComplete.map_algebraMap_iff I H).mpr
      (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton s))
  intro X f _ _ K
  apply SourceCoefficients.complete_source_coefficients_of_quotients H f J K
  intro n
  let A := CommRingCat.of (H ⧸ J ^ n)
  let ψ : H ⟶ A := CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))
  let φ : R ⟶ A := CommRingCat.ofHom
    ((Ideal.Quotient.mk (J ^ n)).comp (algebraMap R H))
  have hφ : Function.Surjective φ :=
    CompletionQuotientCoordinates.completion_quotient_base_surjective I (Submodule.fg_span_singleton s) n
  have hn : RingHom.ker φ.hom ≠ ⊥ := CompletionQuotientStrictness.principal_completion_quotient_kernel_ne_bot s hs n
  exact hquot A φ hφ hn (pullback f (Spec.map ψ))
    (pullback.snd f (Spec.map ψ)) (K.comap (pullback.fst f (Spec.map ψ)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineCoefficientProperty
