import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Classifier

/-! # Classifier Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The smooth Hilbert classifier commutes with arbitrary test-scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_smooth
    {T V : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P) [Smooth F.family.scheme.hom] (f : V ⟶ T) :
    Smooth (F.pullback f).family.scheme.hom :=
  F.family.pullbackAlong_smooth (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n)

theorem SmoothHilbert.ClassifierNaturality.smoothHilbertClassifier_natural
    {S : Scheme.{u}} {T V : Over S} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom] (f : V ⟶ T) :
    letI : Smooth (F.pullback f.left).family.scheme.hom := F.pullback_smooth f.left
    SmoothHilbert.Classifier.smoothHilbertClassifier (F.pullback f.left) = f ≫ SmoothHilbert.Classifier.smoothHilbertClassifier F := by
  have : Smooth (F.pullback f.left).family.scheme.hom := F.pullback_smooth f.left
  symm
  apply SmoothHilbert.Classifier.smoothHilbertClassifier_unique
  exact ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_comp (SmoothHilbert.Classifier.smoothHilbertClassifier F).left f.left).symm.trans
    (congrArg (fun H => H.pullback f.left) (SmoothHilbert.Classifier.smoothHilbertClassifier_classifies F))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
