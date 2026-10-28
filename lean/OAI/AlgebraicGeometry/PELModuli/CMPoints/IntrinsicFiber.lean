import OAI.AlgebraicGeometry.PELModuli.CMPoints.Standard
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Iso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Intrinsic Fiber -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber

noncomputable section

section

/-! The native abelian variety attached to an actual complex point
of the fine PEL model, with its literal universal-family fiber retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def nativePolarizedAt {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (P.abelian.pullback p)
    (AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
      (P.geometricFiber_projectivePresentation ℂ p))

def nativePolarizedAtIso {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    (nativePolarizedAt P p).toOver ≅ (P.abelian.pullback p).scheme :=
  AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso (P.abelian.pullback p) _

theorem nativePolarizedAt_standardModuli (M : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) :
    nativePolarizedAt M.universal.polarized p = (Standard.standardModuliOfArithmetic M).abelianAt p := rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ)

def finePELComplexPoint (x : M.ComplexPoints κ) : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space.left :=
  x.left ≫ CategoryTheory.Limits.pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ))

def nativeFinePELAt (x : M.ComplexPoints κ) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  nativePolarizedAt M.universal.polarized (finePELComplexPoint M κ x)

omit [NumberField K] in
theorem finePELComplexPoint_base (x : M.ComplexPoints κ) :
    finePELComplexPoint M κ x ≫ M.space.hom = Spec.map (CommRingCat.ofHom κ) := by
  change (x.left ≫ CategoryTheory.Limits.pullback.fst M.space.hom
    (Spec.map (CommRingCat.ofHom κ))) ≫ M.space.hom = _
  dsimp [AbelianModuli.ReferenceFamily.Models.FinePELModel.complexFiber, Over.pullback] at *
  rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc]
  have hx : x.left ≫ CategoryTheory.Limits.pullback.snd M.space.hom
      (Spec.map (CommRingCat.ofHom κ)) = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := x.w
  exact (congrArg (fun g : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.complexBase =>
    g ≫ Spec.map (CommRingCat.ofHom κ)) hx).trans (Category.id_comp _)

end

/-! CM invariance for the actual universal abelian fibers under pullback
and polarization-preserving isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def nativePolarizedAtPullbackIso {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T) :
    (nativePolarizedAt (P.pullback f) p).toOver ≅
      (nativePolarizedAt P (p ≫ f)).toOver :=
  nativePolarizedAtIso (P.pullback f) p ≪≫
    (P.abelian.pullbackCompIso f p).symm ≪≫
      (nativePolarizedAtIso P (p ≫ f)).symm

theorem nativePolarizedAt_pullback_hasCMH1_iff
    {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T) :
    (nativePolarizedAt (P.pullback f) p).HasCMH1 ↔
      (nativePolarizedAt P (p ≫ f)).HasCMH1 :=
  Iso.hasCMH1_iso_iff (nativePolarizedAtPullbackIso P f p)

def nativePolarizedAtIsoOfIso {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {P Q : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : P.abelian.scheme ≅ Q.abelian.scheme) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    (nativePolarizedAt P p).toOver ≅ (nativePolarizedAt Q p).toOver :=
  nativePolarizedAtIso P p ≪≫ (Over.pullback p).mapIso e ≪≫
    (nativePolarizedAtIso Q p).symm

theorem nativePolarizedAt_iso_hasCMH1_iff
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {P Q : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : P.abelian.scheme ≅ Q.abelian.scheme) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    (nativePolarizedAt P p).HasCMH1 ↔ (nativePolarizedAt Q p).HasCMH1 :=
  Iso.hasCMH1_iso_iff (nativePolarizedAtIsoOfIso e p)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber
