import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.LevelCover

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Polarization positivity supplies the projective embedding needed by
native complex torsion. In particular the auxiliary level is constructed
from the actual polarization, independently of the prescribed marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}

/-- Every polarized complex abelian scheme has an ordered full level
at every positive integer, constructed through its native exponential. -/
def Polarized.Torsion.polarizedComplexFullLevel
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : ℕ) [NeZero L] : A.abelian.FullLevel L :=
  Complex.ComplexLevel.fullLevel A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) L

namespace Polarized.Torsion.LevelCover

variable {S : Scheme.{0}}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) {L : ℕ} [NeZero L]

theorem polarized_point_mem_fullFrame_image (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (x : Foundations.Scheme.ProjectiveSpace.complexBase) :
    q x ∈ Set.range (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom := by
  let β := polarizedComplexFullLevel (A.pullback q) L
  let f := Frame.Factorization.LevelCover.fullFrameOfRelativeLevel A.abelian p (Over.mk q) β
  exact ⟨f.left x, congrArg (fun h : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S => h x) f.w⟩

theorem polarizedFullFrame_nonempty_of_complex_fiber (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    Nonempty (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).left :=
  Level.CoverIs.LevelCover.fullFrame_nonempty_of_complex_fiber A.abelian p q
    (Projectivity.polarizedNativeProjectivePresentation (A.pullback q))

/-- One complex point of a connected polarized family suffices; its
projectivity and torsion marking are derived from the polarization. -/
theorem polarizedFullFrame_surjective_of_complex_fiber [PreconnectedSpace S]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) : Surjective (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom :=
  Level.CoverIs.LevelCover.fullFrame_surjective_of_complex_fiber A.abelian p q
    (Projectivity.polarizedNativeProjectivePresentation (A.pullback q))

end Polarized.Torsion.LevelCover

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s L : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : PEL.Objects.PELObject P iota N T) [NeZero L]

theorem PEL.Objects.PELObject.auxiliaryLevelProjection_surjective_of_complex_point [PreconnectedSpace T.left]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T.left) : Surjective (PEL.Objects.PELObject.auxiliaryLevelProjection A (L := L)).left :=
  Polarized.Torsion.LevelCover.polarizedFullFrame_surjective_of_complex_fiber A.polarized T.hom q

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
