import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AddedLevelModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso

/-! # Added Level Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

section

/-! Classification of two-level pure families by the constructed
finite-etale full-frame scheme over the exact pure HilbertConstruction model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [CharZero K]
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Fine.PurePolarizedModel g δ L (Spec (.of K))) [NeZero N]

def Fine.PurePolarizedModel.frameToAddedMap {T : Over (Spec (.of K))} (f : T ⟶ M.space)
    (q : Over.mk f.left ⟶ Fine.PurePolarizedModel.prescribedFrame M (N := N)) : T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N) :=
  Over.homMk q.left (by
    exact (Category.assoc q.left (Fine.PurePolarizedModel.prescribedFrame M (N := N)).hom M.space.hom).symm.trans
      ((congrArg (fun z => z ≫ M.space.hom) q.w).trans f.w))

def Fine.PurePolarizedModel.addedMapFrame {T : Over (Spec (.of K))} (j : T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N))
    (f : T ⟶ M.space) (hf : j ≫ Fine.PurePolarizedModel.addedLevelForget M = f) :
    Over.mk f.left ⟶ Fine.PurePolarizedModel.prescribedFrame M (N := N) :=
  Over.homMk j.left (congrArg (fun z => z.left) hf)

def Fine.PurePolarizedModel.frameAddedIso {T : Over (Spec (.of K))} (f : T ⟶ M.space)
    (q : Over.mk f.left ⟶ Fine.PurePolarizedModel.prescribedFrame M (N := N)) :
    Level.Data.AddedFullLevel.Iso ((Fine.PurePolarizedModel.addedLevelUniversal M).pullback (Fine.PurePolarizedModel.frameToAddedMap M f q).left)
      (RelativeLevelIso.relativeAddedLevel M.universal (Over.mk f.left)
        ((Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom).restrict q)) :=
  RelativeLevelIso.relativeAddedLevelIso M.universal q (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom)

end

/-! Classification of two-level pure families by the constructed
finite-etale full-frame scheme over the exact pure HilbertConstruction model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [CharZero K]
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Fine.PurePolarizedModel g δ L (Spec (.of K))) [NeZero N]

theorem Fine.PurePolarizedModel.addedLevel_classifying_exists (hM : M.IsFine)
    (T : Over (Spec (.of K))) (A : Level.Data.AddedFullLevel g δ L N T.left) :
    ∃ j : T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N),
      Nonempty (Level.Data.AddedFullLevel.Iso ((Fine.PurePolarizedModel.addedLevelUniversal M).pullback j.left) A) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hM T A.auxiliary
  let β : (M.universal.abelian.pullback f.left).FullLevel N :=
    @HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g N T.left A.auxiliary.abelian
      (M.universal.abelian.pullback f.left) A.prescribed e.abelian.symm e.symm.abelianGroup
  let q : Over.mk f.left ⟶ Fine.PurePolarizedModel.prescribedFrame M (N := N) :=
    (Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).symm β
  have hβ : (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom).restrict q = β :=
    (Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).apply_symm_apply β
  refine ⟨Fine.PurePolarizedModel.frameToAddedMap M f q, ⟨(Fine.PurePolarizedModel.frameAddedIso M f q).trans
    { auxiliary := e, prescribed := ?_ }⟩⟩
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  have h := congrArg (fun α : (M.universal.abelian.pullback f.left).FullLevel N =>
    (α.hom.app (.op U) c).val ≫ e.abelian.hom) hβ
  exact h.trans (by
    change ((A.prescribed.hom.app (.op U) c).val ≫ e.abelian.inv) ≫ e.abelian.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
