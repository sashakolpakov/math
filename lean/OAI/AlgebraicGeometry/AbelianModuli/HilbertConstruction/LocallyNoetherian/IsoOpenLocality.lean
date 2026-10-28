import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.PreservationRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.CanonicalDual

/-! # Iso Open Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Local complete moduli isomorphisms with a common abelian component determine a complete global isomorphism on every test of fixed locally Noetherian families. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}

def Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_abelian_locallyNoetherian
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
    (T : Over S)
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme)
    [IsMonHom e.hom] (C : Scheme.OpenCover.{v} T.left)
    (a : ∀ i, Moduli.Isomorphisms.LevelPreservingIso ((A.pullback T.hom).pullback (C.f i))
      ((B.pullback T.hom).pullback (C.f i)))
    (ha : ∀ i, (a i).abelian.hom = (Over.pullback (C.f i)).map e.hom) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) := by
  let d := ((A.pullback T.hom).dual.familyComparisonIso (B.pullback T.hom).dual e).hom
  have hD := A.baseChanged_familyComparisonIso_poincare B T.hom e
  have hlocal := fun i => Moduli.Isomorphisms.LevelPreservingIso.pullback_preservation_conditions (A.pullback T.hom)
    (B.pullback T.hom) e.hom d hD (C.f i) (a i) (ha i)
  exact Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual_locallyNoetherianBaseChange A B hδ T e
    (HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hlocal i).1))
    (Level.PreservationOpenLocality.fullLevel_preserves_of_openCover _ _ e.hom C (fun i => (hlocal i).2))

theorem Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_abelian_locallyNoetherian_hom
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
    (T : Over S)
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme)
    [IsMonHom e.hom] (C : Scheme.OpenCover.{v} T.left)
    (a : ∀ i, Moduli.Isomorphisms.LevelPreservingIso ((A.pullback T.hom).pullback (C.f i))
      ((B.pullback T.hom).pullback (C.f i)))
    (ha : ∀ i, (a i).abelian.hom = (Over.pullback (C.f i)).map e.hom) :
    (Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_abelian_locallyNoetherian A B hδ T e C a ha).abelian.hom = e.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
