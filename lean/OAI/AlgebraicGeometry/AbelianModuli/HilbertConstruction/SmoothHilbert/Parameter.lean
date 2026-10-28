import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamilySmoothOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Parameter

noncomputable section

/-! The smooth Hilbert parameter is the actual open subscheme of the specified Hilbert parameter, with a smooth universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def smoothHilbertParameter (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) : Over S :=
  Open.ParameterPoints.openParameterScheme (Hilbert.ParameterScheme.hilbertParameterScheme S n P) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen

def smoothHilbertParameterInclusion (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    smoothHilbertParameter S n P ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P :=
  Open.ParameterPoints.openParameterInclusion (Hilbert.ParameterScheme.hilbertParameterScheme S n P) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen

def smoothHilbertUniversalFamily (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily (smoothHilbertParameter S n P).left n P :=
  (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (smoothHilbertParameterInclusion S n P).left

theorem smoothHilbertUniversalFamily_smooth (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    Smooth (smoothHilbertUniversalFamily S n P).family.scheme.hom := by
  apply ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_smooth_iff_range (smoothHilbertParameterInclusion S n P).left).mpr
  rintro _ ⟨t, rfl⟩
  exact t.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Parameter
