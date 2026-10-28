import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralComponents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComponentSection

/-! # Torsor Integral Component -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorIntegralComponent.Construction

noncomputable section

/-!
# Completion: the integral component of an actual product torsor containing an axis

Smoothness proves that the actual connected component is integral. The
axis lift factors through that component, and its relative normalization
is the second factor by the proved integral-section argument.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] {A B : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q]
  {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q))

instance productTorsor_isNoetherian : IsNoetherian E.gluedScheme :=
  Proper.FiberComponents.Construction.properField_isNoetherian K (TorsorNormalization.Construction.productTorsorToFactor p q E ≫ q)

variable [Smooth p] [Smooth q]

/-- Every connected component of the actual finite étale product torsor is integral. -/
theorem productTorsor_component_isIntegral (x : E.gluedScheme) :
    IsIntegral (Proper.FiberComponents.Construction.noetherianComponentOpen E.gluedScheme x).toScheme := by
  have : Etale E.gluedSchemeToBase := E.gluedSchemeToBase_etale
  have : Smooth (TorsorNormalization.Construction.productTorsorToFactor p q E ≫ q) := by
    unfold TorsorNormalization.Construction.productTorsorToFactor
    infer_instance
  exact SmoothIntegralComponents.Construction.smooth_noetherian_component_isIntegral K (TorsorNormalization.Construction.productTorsorToFactor p q E ≫ q) x

/-- The component containing an actual vanishing axis is integral and has the second factor
as its relative normalization. The axis lift and section identities are retained. -/
theorem productTorsor_axis_integralComponent [PreconnectedSpace B]
    (b : B) (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    ∃ (U : E.gluedScheme.Opens) (_ : IsIntegral U.toScheme)
      (_ : IsClosedImmersion U.ι) (t : B ⟶ U.toScheme),
      t ≫ U.ι ≫ E.gluedSchemeToBase = Proper.AffineBaseChange.Construction.properProductSection p q e he ∧
      t ≫ (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E) = 𝟙 B ∧
      IsIso (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E).fromNormalization := by
  obtain ⟨s, hs⟩ := (E.pullback_eq_zero_iff_lift (Proper.AffineBaseChange.Construction.properProductSection p q e he)).mp h
  let U := Proper.FiberComponents.Construction.noetherianComponentOpen E.gluedScheme (s b)
  have : IsIntegral U.toScheme := productTorsor_component_isIntegral p q E (s b)
  have ht : s ≫ TorsorNormalization.Construction.productTorsorToFactor p q E = 𝟙 B := by
    rw [TorsorNormalization.Construction.productTorsorToFactor, ← Category.assoc, hs]
    exact pullback.lift_snd _ _ _
  let t := ComponentSection.Construction.schemeMapToComponent s b
  have hts : t ≫ (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E) = 𝟙 B :=
    ComponentSection.Construction.schemeMapToComponent_section s b (TorsorNormalization.Construction.productTorsorToFactor p q E) ht
  refine ⟨U, inferInstance, inferInstance, t, ?_, hts, ?_⟩
  · rw [← Category.assoc, ComponentSection.Construction.schemeMapToComponent_ι, hs]
  · exact IntegralSectionIso.Construction.integralProperFamily_section_fromNormalization_isIso
      (U.ι ≫ TorsorNormalization.Construction.productTorsorToFactor p q E) t hts

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorIntegralComponent.Construction
