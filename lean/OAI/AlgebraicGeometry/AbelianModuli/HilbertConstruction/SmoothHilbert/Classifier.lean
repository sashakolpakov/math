import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalClassification

/-! # Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Classifier

noncomputable section

/-! Canonical chosen Hilbert classifiers for smooth families on arbitrary test schemes, with exact recovery and uniqueness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]

def smoothHilbertClassifier : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P :=
  (UniversalClassification.hilbertUniversalFamily_existsUnique_smooth F).exists.choose

theorem smoothHilbertClassifier_classifies :
    (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (smoothHilbertClassifier F).left = F :=
  (UniversalClassification.hilbertUniversalFamily_existsUnique_smooth F).exists.choose_spec

theorem smoothHilbertClassifier_unique (g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hg : (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.left = F) : g = smoothHilbertClassifier F :=
  (UniversalClassification.hilbertUniversalFamily_existsUnique_smooth F).unique hg (smoothHilbertClassifier_classifies F)

theorem smoothHilbertClassifier_injective
    (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth G.family.scheme.hom]
    (h : smoothHilbertClassifier F = smoothHilbertClassifier G) : F = G :=
  (smoothHilbertClassifier_classifies F).symm.trans
    ((congrArg (fun g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P =>
      (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.left) h).trans (smoothHilbertClassifier_classifies G))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Classifier
