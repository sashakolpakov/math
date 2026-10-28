import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AddedLevelExistence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PureTorsionRigidity

/-! # Added Level Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! Classification of two-level pure families by the constructed
finite-etale full-frame scheme over the exact pure HilbertConstruction model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [CharZero K]
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Fine.PurePolarizedModel g δ L (Spec (.of K))) [NeZero N]

variable [Countable K] [LocallyOfFiniteType M.space.hom]

theorem Fine.PurePolarizedModel.addedLevel_classifying_unique (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A : Level.Data.AddedFullLevel g δ L N T.left)
    (j k : T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N))
    (a : Level.Data.AddedFullLevel.Iso ((Fine.PurePolarizedModel.addedLevelUniversal M).pullback j.left) A)
    (b : Level.Data.AddedFullLevel.Iso ((Fine.PurePolarizedModel.addedLevelUniversal M).pullback k.left) A) : j = k := by
  let f := j ≫ Fine.PurePolarizedModel.addedLevelForget M
  let h := k ≫ Fine.PurePolarizedModel.addedLevelForget M
  let q := Fine.PurePolarizedModel.addedMapFrame M j f rfl
  let r := Fine.PurePolarizedModel.addedMapFrame M k h rfl
  let a' := (Fine.PurePolarizedModel.frameAddedIso M f q).symm.trans a
  let b' := (Fine.PurePolarizedModel.frameAddedIso M h r).symm.trans b
  obtain ⟨u, _, hu⟩ := hM T A.auxiliary
  have hh : h = f := (hu h ⟨b'.auxiliary⟩).trans (hu f ⟨a'.auxiliary⟩).symm
  let r' := Fine.PurePolarizedModel.addedMapFrame M k f hh
  let c := (Fine.PurePolarizedModel.frameAddedIso M f r').symm.trans b
  let firstLevel := (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom).restrict q
  let secondLevel := (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel M.universal.abelian M.space.hom).restrict r'
  have hi := M.prescribed_level_transport_independent hM hL T (M.universal.pullback f.left)
    A.auxiliary a'.auxiliary c.auxiliary secondLevel
  have hβ : firstLevel = secondLevel := by
    apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    intro U coefficients
    apply (cancel_mono a'.auxiliary.abelian.hom).mp
    have he := congrArg (fun α : A.auxiliary.abelian.FullLevel N =>
      (α.hom.app (.op U) coefficients).val) hi
    exact (a'.prescribed_basis U coefficients).trans
      (he.trans (c.prescribed_basis U coefficients)).symm
  have hq : q = r' :=
    (Frame.Factorization.LevelCover.fullFramePointsEquiv M.universal.abelian M.space.hom (Over.mk f.left)).injective hβ
  exact Over.OverMorphism.ext (congrArg (fun z => z.left) hq)

theorem Fine.PurePolarizedModel.addedLevel_isFine (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A : Level.Data.AddedFullLevel g δ L N T.left) :
    ∃! j : T ⟶ Fine.PurePolarizedModel.addedLevelSpace M (N := N),
      Nonempty (Level.Data.AddedFullLevel.Iso ((Fine.PurePolarizedModel.addedLevelUniversal M).pullback j.left) A) := by
  obtain ⟨j, ⟨a⟩⟩ := M.addedLevel_classifying_exists hM T A
  refine ⟨j, ⟨a⟩, ?_⟩
  rintro k ⟨b⟩
  exact M.addedLevel_classifying_unique hM hL T A k j b a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
