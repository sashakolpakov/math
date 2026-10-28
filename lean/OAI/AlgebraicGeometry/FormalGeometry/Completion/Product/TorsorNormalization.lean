import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.SchemeBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionIso
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange

/-! # Torsor Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorNormalization.Construction

noncomputable section

/-!
# Completion: normalization of an actual product torsor trivial on a section axis

Vanishing of the actual axis restriction supplies a geometric section of
the torsor family over the other factor. If its total space is integral,
the proved split-integral argument identifies its relative normalization
with that factor. Connectedness of the fibers remains to be proved.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] {A B : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p]
  (q : B ⟶ Spec (CommRingCat.of K))
  {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q))

/-- The proper family underlying the actual finite étale product torsor. -/
def productTorsorToFactor : E.gluedScheme ⟶ B :=
  E.gluedSchemeToBase ≫ pullback.snd p q

instance productTorsorToFactor_isProper : IsProper (productTorsorToFactor p q E) := by
  have : IsFinite E.gluedSchemeToBase := E.gluedSchemeToBase_finite
  unfold productTorsorToFactor
  infer_instance

omit [IsProper p] in
/-- Actual vanishing on the section axis gives an actual section of the proper torsor family. -/
theorem productTorsorToFactor_hasSection
    (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    ∃ s : B ⟶ E.gluedScheme, s ≫ productTorsorToFactor p q E = 𝟙 B := by
  obtain ⟨s, hs⟩ := (E.pullback_eq_zero_iff_lift (Proper.AffineBaseChange.Construction.properProductSection p q e he)).mp h
  refine ⟨s, ?_⟩
  rw [productTorsorToFactor, ← Category.assoc, hs]
  exact pullback.lift_snd _ _ _

/-- For an integral total torsor, vanishing on the section axis identifies its relative
normalization with the actual second factor. -/
theorem productTorsor_fromNormalization_isIso [IsIntegral E.gluedScheme]
    (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 E.extClass = 0) :
    IsIso (productTorsorToFactor p q E).fromNormalization := by
  obtain ⟨s, hs⟩ := productTorsorToFactor_hasSection p q E e he h
  exact IntegralSectionIso.Construction.integralProperFamily_section_fromNormalization_isIso
    (productTorsorToFactor p q E) s hs

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorNormalization.Construction
