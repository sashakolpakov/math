import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniversalLevelRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareEquivalence

/-! # Universal Level Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.UniversalLevelRigidity

noncomputable section

/-! Full-level polarized isomorphisms of fixed families over a locally Noetherian base are unique after every scheme base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hN : 3 ≤ N) (T : Over S) :
    Subsingleton (Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)) := by
  let C := S.affineOpenCover.openCover
  refine ⟨fun e d => ?_⟩
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks (C.pullback₁ T.hom)
  intro i
  change S.affineOpenCover.I₀ at i
  have : IsAffine (C.X i) := inferInstanceAs (IsAffine (Spec (S.affineOpenCover.X i)))
  have hi : IsOpenImmersion (C.f i) := C.map_prop i
  have : IsLocallyNoetherian (C.X i) :=
    @isLocallyNoetherian_of_isOpenImmersion (C.X i) S (C.f i) hi inferInstance
  have : IsNoetherianRing Γ(C.X i, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let p := Limits.pullback.fst T.hom (C.f i)
  let q := Limits.pullback.snd T.hom (C.f i)
  have hs : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso ((A.pullback (C.f i)).pullback q)
      ((B.pullback (C.f i)).pullback q)) :=
    Noetherian.UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_noetherian_affine
      (A.pullback (C.f i)) (B.pullback (C.f i)) hN (Over.mk q)
  have : Subsingleton (Moduli.Isomorphisms.LevelPreservingIso ((A.pullback T.hom).pullback p)
      ((B.pullback T.hom).pullback p)) :=
    (Moduli.Isomorphisms.LevelPreservingIso.baseSquareEquiv A B T.hom (C.f i) p q
      (Limits.pullback.condition (f := T.hom) (g := C.f i))).injective.subsingleton
  exact congrArg (fun z : Moduli.Isomorphisms.LevelPreservingIso ((A.pullback T.hom).pullback p)
    ((B.pullback T.hom).pullback p) => z.abelian.hom) (Subsingleton.elim (e.pullback p) (d.pullback p))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.UniversalLevelRigidity
