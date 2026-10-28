import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Fiber Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Concrete consequences of ample projective presentations for relative ample
bundles and the geometric fibers of HilbertConstruction polarized abelian data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

/-- A relatively ample bundle on a proper scheme gives projective presentations
over every affine open of the base. -/
def Line.Bundles.LineBundle.IsRelativelyAmple.localProjectivePresentation {L : Line.Bundles.LineBundle X}
    {f : X ⟶ S} (hL : L.IsRelativelyAmple f) [IsProper f]
    (U : S.Opens) (hU : IsAffineOpen U) :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (f ∣_ U)) := by
  have : IsAffine U.toScheme := hU
  exact (hL U hU).projectivePresentation (f ∣_ U)

/-- Positivity in the polarization data gives an actual projective presentation
of each geometric abelian fiber. -/
theorem PolarizationData.Polarization.geometricFiber_projectivePresentation {D : Dual.Data.DualAbelianData A}
    {δ : Fin g → ℕ} (p : PolarizationData.Polarization D δ) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) :
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (A.pullback s).scheme) := by
  obtain ⟨L, hL, _⟩ := p.positive K s
  exact hL.exists_projectivePresentation (A.pullback s).scheme.hom

/-- A chosen closed embedding of a geometric fiber of a polarized full-level object. -/
def PolarizationData.PolarizedAbelianWithFullLevel.geometricFiber_projectivePresentation
    {δ : Fin g → ℕ} {N : ℕ} (M : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    Projective.ProjectivePresentations.ProjectivePresentation (M.abelian.pullback s).scheme :=
  (M.polarization.geometricFiber_projectivePresentation K s).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
