import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveBaseChange

/-! # Fine Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! The full all-test pure moduli property and the actual projective
presentation persist under arbitrary scheme base change. The classifying
map comparison uses the actual pullback adjunction and polarized-family
composition isomorphism, including Poincare and ordered level data.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme.{0}}

def Fine.PurePolarizedModel.pullback (M : Fine.PurePolarizedModel g δ N S) (f : T ⟶ S) :
    Fine.PurePolarizedModel g δ N T where
  space := (Over.pullback f).obj M.space
  universal := M.universal.pullback (pullback.fst M.space.hom f)

def Fine.PurePolarizedModel.pullbackClassifyingIso
    (M : Fine.PurePolarizedModel g δ N S) (f : T ⟶ S) (X : Over T)
    (k : X ⟶ (M.pullback f).space) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((M.pullback f).universal.pullback k.left)
      (M.universal.pullback (((Over.mapPullbackAdj f).homEquiv X M.space).symm k).left) := by
  change HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    ((M.universal.pullback (pullback.fst M.space.hom f)).pullback k.left)
    (M.universal.pullback (k.left ≫ pullback.fst M.space.hom f))
  exact HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal (pullback.fst M.space.hom f) k.left

theorem Fine.PurePolarizedModel.IsFine.pullback
    {M : Fine.PurePolarizedModel g δ N S} (hM : M.IsFine) (f : T ⟶ S) :
    (M.pullback f).IsFine := by
  intro X A
  let F := (Over.mapPullbackAdj f).homEquiv X M.space
  obtain ⟨a, ⟨ha⟩, huniq⟩ := hM ((Over.map f).obj X) A
  let k : X ⟶ (M.pullback f).space := F a
  have hk : F.symm k = a := F.symm_apply_apply a
  have e := M.pullbackClassifyingIso f X k
  change HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((M.pullback f).universal.pullback k.left)
    (M.universal.pullback (F.symm k).left) at e
  rw [hk] at e
  refine ⟨k, ⟨e.trans ha⟩, ?_⟩
  intro k' hk'
  obtain ⟨hk'⟩ := hk'
  apply F.symm.injective
  rw [hk]
  exact huniq (F.symm k') ⟨(M.pullbackClassifyingIso f X k').symm.trans hk'⟩

theorem Fine.PurePolarizedModel.quasiProjective_pullback
    (M : Fine.PurePolarizedModel g δ N S)
    (hM : Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)) (f : T ⟶ S) :
    Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (M.pullback f).space) := by
  obtain ⟨P⟩ := hM
  exact ⟨P.baseChange f⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
