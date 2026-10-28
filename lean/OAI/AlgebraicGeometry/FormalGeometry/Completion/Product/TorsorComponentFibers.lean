import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleProductCoverConnected
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorIntegralComponent

/-! # Torsor Component Fibers -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorComponentFibers.Construction

noncomputable section

/-! The actual component containing an axis lift has connected fibers over the other factor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Scheme.{u}}
  [IsIntegral A] [IsIntegral B]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q))

/-- The integral component selected by the actual axis lift has connected scheme-theoretic
fibers, derived from its actual normalized formal-functions comparison. -/
theorem productTorsor_axis_integralComponent_connectedFibers
    (b : B) (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    ∃ (U : E.gluedScheme.Opens) (_ : IsIntegral U.toScheme)
      (_ : IsClosedImmersion U.ι) (s : B ⟶ U.toScheme),
      s ≫ U.ι ≫ E.gluedSchemeToBase = Proper.AffineBaseChange.Construction.properProductSection p q e he ∧
      s ≫ (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E) = 𝟙 B ∧
      IsIso (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E).fromNormalization ∧
      ∀ y : B, ConnectedSpace ((U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E).fiber y) := by
  obtain ⟨U, hU, hc, s, hs, hsect, hN⟩ := TorsorIntegralComponent.Construction.productTorsor_axis_integralComponent p q E b e he h
  have : IsIntegral U.toScheme := hU
  have : IsClosedImmersion U.ι := hc
  have : IsFinite E.gluedSchemeToBase := E.gluedSchemeToBase_finite
  have : Etale E.gluedSchemeToBase := E.gluedSchemeToBase_etale
  let t := U.ι ≫ E.gluedSchemeToBase
  have : IsFinite t := inferInstanceAs (IsFinite (U.ι ≫ E.gluedSchemeToBase))
  have : Etale t := inferInstanceAs (Etale (U.ι ≫ E.gluedSchemeToBase))
  have hf : t ≫ pullback.snd p q = U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E := by
    dsimp [t, TorsorNormalization.Construction.productTorsorToFactor]
    rw [Category.assoc]
  have hsect' : s ≫ (t ≫ pullback.snd p q) = 𝟙 B := by rw [hf]; exact hsect
  have : IsIso (t ≫ pullback.snd p q).fromNormalization :=
    IntegralSectionIso.Construction.integralProperFamily_section_fromNormalization_isIso (t ≫ pullback.snd p q) s hsect'
  refine ⟨U, hU, hc, s, hs, hsect, hN, fun y => ?_⟩
  have hy := Finite.EtaleProductCoverConnected.Construction.finiteEtaleProductCover_fiber_connected p q t y
  rw [hf] at hy
  exact hy

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorComponentFibers.Construction
