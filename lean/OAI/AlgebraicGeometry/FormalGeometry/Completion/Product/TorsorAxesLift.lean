import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorComponentFibers
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverAxisFiber
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.SubcoverDegreeOne
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleDegreeOne

/-! # Torsor Axes Lift -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorAxesLift.Construction

noncomputable section

/-! Vanishing on both axes gives an actual global section of the finite-coefficient product torsor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p] [GeometricallyIntegral p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [GeometricallyIntegral q]
  {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q))
  (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
  (b : Spec (CommRingCat.of K) ⟶ B) (hb : b ≫ q = 𝟙 _)

/-- Both actual vanishing axis restrictions force a global section of the actual torsor.
The component degree is proved to be one using its connected fiber and the opposite-axis trivialization. -/
theorem productTorsor_axes_hasSection
    (hfirst : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1 E.extClass = 0)
    (hsecond : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    ∃ s : pullback p q ⟶ E.gluedScheme, s ≫ E.gluedSchemeToBase = 𝟙 _ := by
  have : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton p
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral A)
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton q
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsIntegral (pullback p q) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd p q)
  have : IsFinite E.gluedSchemeToBase := E.gluedSchemeToBase_finite
  have : Etale E.gluedSchemeToBase := E.gluedSchemeToBase_etale
  obtain ⟨U, hU, hc, s, _hs, hsect, _hN, _hfibers⟩ :=
    TorsorComponentFibers.Construction.productTorsor_axis_integralComponent_connectedFibers p q E
      (b (IsLocalRing.closedPoint K)) e he hsecond
  have : IsIntegral U.toScheme := hU
  have : IsClosedImmersion U.ι := hc
  let t := U.ι ≫ E.gluedSchemeToBase
  have : IsFinite t := inferInstanceAs (IsFinite (U.ι ≫ E.gluedSchemeToBase))
  have : Etale t := inferInstanceAs (Etale (U.ι ≫ E.gluedSchemeToBase))
  have hs' : s ≫ (t ≫ pullback.snd p q) = 𝟙 B := by
    simpa only [t, Category.assoc, TorsorNormalization.Construction.productTorsorToFactor] using hsect
  have : IsIso (t ≫ pullback.snd p q).fromNormalization :=
    IntegralSectionIso.Construction.integralProperFamily_section_fromNormalization_isIso (t ≫ pullback.snd p q) s hs'
  let axis := (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left
  have : ConnectedSpace (pullback t axis : Scheme.{u}) := CoverAxisFiber.Construction.productCover_firstAxis_connected p q t b hb
  have : IsIso (pullback.snd t axis) := E.connectedSubcover_baseChange_isIso axis U.ι hfirst
  have : IsIso t := Finite.EtaleDegreeOne.Construction.finite_flat_isIso_of_baseChange_isIso t axis
  refine ⟨inv t ≫ U.ι, ?_⟩
  rw [Category.assoc]
  exact IsIso.inv_hom_id t

/-- The actual finite-coefficient extension class vanishes when both axis restrictions vanish. -/
theorem productTorsor_class_eq_zero_of_axes
    (hfirst : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1 E.extClass = 0)
    (hsecond : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    E.extClass = 0 :=
  E.class_eq_zero_iff_scheme_section.mpr (productTorsor_axes_hasSection p q E e he b hb hfirst hsecond)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorAxesLift.Construction
