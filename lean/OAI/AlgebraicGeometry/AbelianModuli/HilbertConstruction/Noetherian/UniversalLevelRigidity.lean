import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalHomFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityProjectiveBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity

/-! # Universal Level Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniversalLevelRigidity

noncomputable section

/-! Full-level isomorphisms of fixed polarized Noetherian families with projective presentations are unique on every test scheme. Over a Noetherian affine base those presentations are constructed from the polarization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem polarizedPullbackIsomorphisms_subsingleton_of_noetherian_projective
    {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (hN : 3 ≤ N) (T : Over S) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)) := by
  refine ⟨fun e d => ?_⟩
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply Relative.UniversalHomFieldDetection.relativeUniversalAbelianHom_eq_of_fieldPullbacks A.abelian B.abelian
    (PA.product PB).embedding T (hfMon := e.abelianGroup) (hqMon := d.abelianGroup)
  intro K _ s
  have := Level.IsomorphismUniquenessOverField.polarizedIsomorphisms_subsingleton_overField
    ((A.pullback T.hom).pullback s) ((B.pullback T.hom).pullback s) hN
  exact congrArg (fun q : Moduli.Isomorphisms.LevelPreservingIso ((A.pullback T.hom).pullback s)
      ((B.pullback T.hom).pullback s) => q.abelian.hom)
    (Subsingleton.elim (e.pullback s) (d.pullback s))

theorem polarizedPullbackIsomorphisms_subsingleton_of_noetherian_affine
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hN : 3 ≤ N) (T : Over S) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)) := by
  have : IsNoetherian S :=
    (isNoetherian_iff_of_finite_iSup_eq_top
      (S := fun _ : Unit => (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)) (by simp)).mpr
        (fun _ => inferInstance)
  exact polarizedPullbackIsomorphisms_subsingleton_of_noetherian_projective A B
    A.projectivePresentation_of_noetherian_affine B.projectivePresentation_of_noetherian_affine hN T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniversalLevelRigidity
