import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleAlgebraReduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Etale Reduced -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced

noncomputable section

/-! Finite etale covers of arbitrary reduced schemes are reduced,
without a noetherian hypothesis on a test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finite_etale_affine_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsReduced Y] [IsFinite f] [Etale f] : IsReduced X := by
  have hf : f.appTop.hom.Finite :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := f)).mp inferInstance).2
  have he : f.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp inferInstance
  algebraize [f.appTop.hom]
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := hf
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := he
  have : _root_.IsReduced Γ(X, ⊤) := EtaleAlgebraReduced.finite_etale_algebra_isReduced Γ(Y, ⊤) Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

theorem finite_etale_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsReduced Y] [IsFinite f] [Etale f] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  change Y.affineCover.I₀ at i
  change IsReduced (CategoryTheory.Limits.pullback f (Y.affineCover.f i))
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have : IsAffine (CategoryTheory.Limits.pullback f (Y.affineCover.f i)) :=
    isAffine_of_isAffineHom (CategoryTheory.Limits.pullback.snd f (Y.affineCover.f i))
  exact finite_etale_affine_isReduced (CategoryTheory.Limits.pullback.snd f (Y.affineCover.f i))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
