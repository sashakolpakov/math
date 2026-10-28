import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Parameter

/-! # Point Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.PointEquivalence

noncomputable section

/-! Points of the actual smooth Hilbert open are equivalent to smooth relative projective Hilbert families over every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def SmoothRelativeProjectiveHilbertFamily (T : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :=
  {F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P // Smooth F.family.scheme.hom}

def smoothHilbertMapFamilyEquiv (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ) :
    {g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P //
      Smooth ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.left).family.scheme.hom} ≃
      SmoothRelativeProjectiveHilbertFamily T.left n P where
  toFun g := ⟨(Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.val.left, g.property⟩
  invFun F := by
    have : Smooth F.val.family.scheme.hom := F.property
    refine ⟨Classifier.smoothHilbertClassifier F.val, ?_⟩
    rw [Classifier.smoothHilbertClassifier_classifies]
    exact F.property
  left_inv g := by
    have : Smooth ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.val.left).family.scheme.hom := g.property
    apply Subtype.ext
    exact (Classifier.smoothHilbertClassifier_unique ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.val.left) g.val rfl).symm
  right_inv F := by
    have : Smooth F.val.family.scheme.hom := F.property
    apply Subtype.ext
    exact Classifier.smoothHilbertClassifier_classifies F.val

def smoothHilbertRangeEquiv (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ) :
    {g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P // Set.range g.left ⊆ (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen} ≃
      {g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P //
        Smooth ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.left).family.scheme.hom} where
  toFun g := ⟨g.val, ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_smooth_iff_range g.val.left).mpr g.property⟩
  invFun g := ⟨g.val, ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_smooth_iff_range g.val.left).mp g.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def smoothHilbertParameterPointEquiv (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ) :
    (T ⟶ Parameter.smoothHilbertParameter S n P) ≃ SmoothRelativeProjectiveHilbertFamily T.left n P :=
  (Open.ParameterPoints.openParameterPointEquiv (Hilbert.ParameterScheme.hilbertParameterScheme S n P) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen T).trans
    ((smoothHilbertRangeEquiv S T n P).trans (smoothHilbertMapFamilyEquiv S T n P))

theorem smoothHilbertParameterPointEquiv_val (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ)
    (g : T ⟶ Parameter.smoothHilbertParameter S n P) :
    (smoothHilbertParameterPointEquiv S T n P g).val =
      (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (g.left ≫ (Parameter.smoothHilbertParameterInclusion S n P).left) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.PointEquivalence
