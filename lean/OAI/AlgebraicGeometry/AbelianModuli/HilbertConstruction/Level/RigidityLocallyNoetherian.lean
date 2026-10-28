import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityProjectiveBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection

/-! # Rigidity Locally Noetherian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityLocallyNoetherian

noncomputable section

/-! Full-level polarized isomorphisms at level at least three are unique over every locally Noetherian base. Required projective presentations are now constructed from the polarization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem polarizedIsomorphisms_subsingleton_of_locallyNoetherian
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hN : 3 ≤ N) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso A B) := by
  refine ⟨fun e d => ?_⟩
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks S.affineOpenCover.openCover
  intro i
  change S.affineOpenCover.I₀ at i
  have : IsAffine (S.affineOpenCover.openCover.X i) :=
    inferInstanceAs (IsAffine (Spec (S.affineOpenCover.X i)))
  have hi : IsOpenImmersion (S.affineOpenCover.openCover.f i) := S.affineOpenCover.openCover.map_prop i
  have : IsLocallyNoetherian (S.affineOpenCover.openCover.X i) :=
    @isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.openCover.X i) S
      (S.affineOpenCover.openCover.f i) hi inferInstance
  let b := S.affineOpenCover.openCover.f i
  have : IsNoetherianRing Γ(S.affineOpenCover.openCover.X i, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have := RigidityProjectiveBase.polarizedIsomorphisms_subsingleton_of_sourceProjective (A.pullback b) (B.pullback b)
    (A.pullback b).projectivePresentation_of_noetherian_affine hN
  exact congrArg (fun q : Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b) => q.abelian.hom)
    (Subsingleton.elim (e.pullback b) (d.pullback b))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityLocallyNoetherian
