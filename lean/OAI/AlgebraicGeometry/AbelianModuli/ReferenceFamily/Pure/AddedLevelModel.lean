import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization

/-! # Added Level Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! Over a pure HilbertConstruction model, the independently prescribed full level is
constructed by the actual finite-etale full-frame scheme. This supplies
the two-level candidate family without restricting the prescribed N. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover

variable {K : Type} [Field K] [CharZero K] {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Fine.PurePolarizedModel g δ L (Spec (.of K))) [NeZero N]

def Fine.PurePolarizedModel.prescribedFrame : Over M.space.left :=
  Frame.Locus.LevelCover.fullFrameScheme M.universal.abelian M.space.hom (N := N)

def Fine.PurePolarizedModel.addedLevelSpace : Over (Spec (.of K)) :=
  (Over.map M.space.hom).obj (Fine.PurePolarizedModel.prescribedFrame M (N := N))

def Fine.PurePolarizedModel.addedLevelForget : Fine.PurePolarizedModel.addedLevelSpace M (N := N) ⟶ M.space :=
  Over.homMk (Fine.PurePolarizedModel.prescribedFrame M (N := N)).hom rfl

instance Fine.PurePolarizedModel.addedLevelForget_isFinite : IsFinite (Fine.PurePolarizedModel.addedLevelForget M (N := N)).left :=
  (Frame.Locus.LevelCover.fullFrameScheme_finite_etale M.universal.abelian M.space.hom).1

instance Fine.PurePolarizedModel.addedLevelForget_etale : Etale (Fine.PurePolarizedModel.addedLevelForget M (N := N)).left :=
  (Frame.Locus.LevelCover.fullFrameScheme_finite_etale M.universal.abelian M.space.hom).2

def Fine.PurePolarizedModel.addedLevelUniversal : Level.Data.AddedFullLevel g δ L N (Fine.PurePolarizedModel.addedLevelSpace M (N := N)).left where
  auxiliary := M.universal.pullback (Fine.PurePolarizedModel.prescribedFrame M (N := N)).hom
  prescribed := Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom

def Fine.PurePolarizedModel.liftPrescribedLevel {T : Over (Spec (.of K))} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N) := by
  let t : Over M.space.left := Over.mk f.left
  let q := (Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom t).symm β
  exact Over.homMk q.left (by
    exact (Category.assoc q.left (Frame.Locus.LevelCover.fullFrameScheme M.universal.abelian M.space.hom).hom
      M.space.hom).symm.trans ((congrArg (fun h => h ≫ M.space.hom) q.w).trans f.w))

theorem Fine.PurePolarizedModel.liftPrescribedLevel_forget {T : Over (Spec (.of K))} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    Fine.PurePolarizedModel.liftPrescribedLevel M f β ≫ Fine.PurePolarizedModel.addedLevelForget M = f := by
  apply Over.OverMorphism.ext
  exact ((Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).symm β).w

theorem Fine.PurePolarizedModel.liftPrescribedLevel_coefficients {T : Over (Spec (.of K))} (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel N) :
    (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom).restrict
      ((Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).symm β) = β :=
  (Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).apply_symm_apply β

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
