import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.HomFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsomorphismUniquenessOverField
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Rigidity Projective Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityProjectiveBase

noncomputable section

/-! Actual polarized isomorphisms preserving a full level of degree at least three are unique over locally noetherian bases when the abelian schemes admit projective presentations. Nonreduced bases are included. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem polarizedIsomorphisms_subsingleton_of_productEmbedding {n : ℕ}
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (hN : 3 ≤ N) : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A B) := by
  refine ⟨fun e d => ?_⟩
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply Embedded.HomFieldDetection.embeddedAbelianHom_eq_of_fieldPullbacks A.abelian B.abelian j
  intro K _ b
  have := IsomorphismUniquenessOverField.polarizedIsomorphisms_subsingleton_overField (A.pullback b) (B.pullback b) hN
  exact congrArg (fun f : Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b) => f.abelian.hom)
    (Subsingleton.elim (e.pullback b) (d.pullback b))

theorem polarizedIsomorphisms_subsingleton_of_projectivePresentations
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (hN : 3 ≤ N) : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A B) :=
  polarizedIsomorphisms_subsingleton_of_productEmbedding A B (PA.product PB).embedding hN

theorem polarizedIsomorphisms_subsingleton_of_sourceProjective
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme) (hN : 3 ≤ N) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A B) := by
  refine ⟨fun e d => ?_⟩
  let PB := PA.ofSourceIso e.abelian.symm
  have := polarizedIsomorphisms_subsingleton_of_projectivePresentations A B PA PB hN
  exact Subsingleton.elim e d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityProjectiveBase
