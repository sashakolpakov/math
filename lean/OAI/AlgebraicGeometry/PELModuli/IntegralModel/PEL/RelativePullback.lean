import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso

/-! # Relative Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! The actual relative PEL pullback comparison has the canonical
pure relative pullback as its polarized component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S T : Scheme.{0}} {g n : ℕ} {δ : Fin g → ℕ}

def Iso.PolarizedActionIso.pullbackCongr (A : Has.PolarizedActionData E g δ n S) (f h : T ⟶ S) (w : f = h) :
    Iso.PolarizedActionIso (A.pullback f) (A.pullback h) := by
  subst h
  exact Iso.PolarizedActionIso.refl _

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.pullbackCongr_polarized (A : Has.PolarizedActionData E g δ n S)
    (f h : T ⟶ S) (w : f = h) :
    (Iso.PolarizedActionIso.pullbackCongr A f h w).polarized = AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.purePullbackCongrIso A.polarized f h w := by
  subst h
  rfl

def Iso.PolarizedActionIso.relativePullback (A : Has.PolarizedActionData E g δ n S) {T U : Over S} (f : T ⟶ U) :
    Iso.PolarizedActionIso ((A.pullback U.hom).pullback f.left) (A.pullback T.hom) :=
  (Iso.PolarizedActionIso.pullbackComp A U.hom f.left).trans (Iso.PolarizedActionIso.pullbackCongr A _ _ f.w)

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.relativePullback_polarized (A : Has.PolarizedActionData E g δ n S)
    {T U : Over S} (f : T ⟶ U) :
    (Iso.PolarizedActionIso.relativePullback A f).polarized = AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.pureRelativePullbackIso A.polarized f := by
  change (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.polarized U.hom f.left).trans
    (Iso.PolarizedActionIso.pullbackCongr A _ _ f.w).polarized = _
  rw [Iso.PolarizedActionIso.pullbackCongr_polarized]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
