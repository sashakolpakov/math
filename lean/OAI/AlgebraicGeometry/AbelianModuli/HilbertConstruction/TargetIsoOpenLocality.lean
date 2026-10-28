import OAI.RepresentationTheory.Hecke.NoetherianTargetPELRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Target Iso Open Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Local complete polarized comparisons to a modeled target recover
one global comparison. The abelian component is specified as an actual
scheme isomorphism; its group equations also descend from the cover.
The source family and test scheme are unrestricted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (e : B.abelian.scheme ≅ (A.pullback f).abelian.scheme)
    (C : T.OpenCover)
    (a : ∀ i, Moduli.Isomorphisms.LevelPreservingIso (B.pullback (C.f i)) ((A.pullback f).pullback (C.f i)))
    (ha : ∀ i, (a i).abelian.hom = (Over.pullback (C.f i)).map e.hom)

/-- Only the target must come from a locally Noetherian model. In
particular neither the source family nor T is assumed Noetherian. -/
def Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget : Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f) := by
  letI : IsMonHom e.hom := by
    apply MonoidHomOpenLocality.isMonHom_of_openCover e.hom C
    intro i
    rw [← ha i]
    exact (a i).abelianGroup
  exact RepresentationTheory.Hecke.NoetherianTargetPELRecovery.OrdinaryCharacterIntrinsic.polarized_comparison_to_noetherian_pullback_of_local A f B e C a ha

theorem Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget_abelian :
    (Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget A f B e C a ha).abelian = e := rfl

/-- The recovered global comparison restricts to every original local
comparison, including its dual and Poincare data. -/
theorem Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget_pullback (i : C.I₀) :
    (Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget A f B e C a ha).pullback (C.f i) = a i := by
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  change (Over.pullback (C.f i)).map e.hom = (a i).abelian.hom
  exact (ha i).symm

theorem Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget_unique (q : Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))
    (hq : q.abelian = e) : q = Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_modeledTarget A f B e C a ha :=
  Moduli.Isomorphisms.LevelPreservingIso.ext_abelian q _ (congrArg Iso.hom hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
