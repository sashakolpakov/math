import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompatibleLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DivisorLevelInt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AddedLevelClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelRelabeling

/-! # Compatible Pure Fine Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Fine pure moduli at a multiple of a fixed tame auxiliary level.
The compatible full-frame locus is finite etale over the original HilbertConstruction
model, retains its quasi-projectivity, and classifies the prescribed
level alone because that marking determines the auxiliary marking. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

section

variable {S T : Scheme.{0}} {g L k : ℕ} {δ : Fin g → ℕ}
  (hL : 0 < L) (hk : 0 < k)

def Level.Data.AddedFullLevel.ofDivisor (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ (L * k) S) :
    Level.Data.AddedFullLevel g δ L (L * k) S where
  auxiliary := {
    abelian := B.abelian
    dual := B.dual
    polarization := B.polarization
    level := B.level.divisor (L := L) (k := k) hL hk }
  prescribed := B.level

def Level.Data.AddedFullLevel.fromAuxiliaryIso (B : Level.Data.AddedFullLevel g δ L (L * k) S)
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L S)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B.auxiliary) : Level.Data.AddedFullLevel g δ L (L * k) S where
  auxiliary := A
  prescribed := @HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g (L * k) S B.auxiliary.abelian A.abelian
    B.prescribed e.abelian.symm e.symm.abelianGroup

def Level.Data.AddedFullLevel.fromAuxiliaryIso_iso (B : Level.Data.AddedFullLevel g δ L (L * k) S)
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L S)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B.auxiliary) : Level.Data.AddedFullLevel.Iso (Level.Data.AddedFullLevel.fromAuxiliaryIso B A e) B where
  auxiliary := e
  prescribed := @Level.IsoCalculus.fullLevel_transport_symm S g (L * k) B.auxiliary.abelian A.abelian
    B.prescribed e.abelian.symm e.symm.abelianGroup

theorem Level.Data.AddedFullLevel.divisor_compatible_of_iso {B C : Level.Data.AddedFullLevel g δ L (L * k) S}
    (e : Level.Data.AddedFullLevel.Iso B C) (hC : C.prescribed.divisor (L := L) (k := k) hL hk = C.auxiliary.level) :
    B.prescribed.divisor (L := L) (k := k) hL hk = B.auxiliary.level := by
  apply Level.IsoCalculus.fullLevel_transport_injective e.auxiliary.abelian
  have he : B.auxiliary.level.transport e.auxiliary.abelian = C.auxiliary.level := by
    apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    exact e.auxiliary.level
  exact (B.prescribed.divisor_transport hL hk e.auxiliary.abelian).trans
    ((congrArg (fun β => β.divisor (L := L) (k := k) hL hk) e.prescribed).trans (hC.trans he.symm))

theorem Level.Data.AddedFullLevel.divisor_compatible_pullback (B : Level.Data.AddedFullLevel g δ L (L * k) S)
    (hB : B.prescribed.divisor (L := L) (k := k) hL hk = B.auxiliary.level) (f : T ⟶ S) :
    (B.pullback f).prescribed.divisor (L := L) (k := k) hL hk = (B.pullback f).auxiliary.level :=
  (B.prescribed.divisor_pullback hL hk f).symm.trans (congrArg (fun β => β.pullback f) hB)

def Level.Data.AddedFullLevel.isoOfDivisorCompatible {B C : Level.Data.AddedFullLevel g δ L (L * k) S}
    (hB : B.prescribed.divisor (L := L) (k := k) hL hk = B.auxiliary.level)
    (hC : C.prescribed.divisor (L := L) (k := k) hL hk = C.auxiliary.level)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B.forgetAuxiliary C.forgetAuxiliary) : Level.Data.AddedFullLevel.Iso B C where
  auxiliary := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := e.polarization
    poincare := e.poincare
    level := by
      intro U c
      rw [← hB, ← hC]
      exact e.level U (DivisorLevelInt.DivisorLevel.sections L k g c) }
  prescribed := by
    apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    exact e.level

end

namespace CompatiblePureFineConstruction.LevelCover

theorem divisorLevelTransformation_apply {S : Scheme.{0}} {g L k : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) [NeZero L] [NeZero k]
    (T : Over S) (β : (A.pullback T.hom).FullLevel (L * k)) :
    (DivisorLevelInt.LevelCover.divisorLevelTransformation A (L := L) (k := k)).app (.op T) β =
      β.divisor (L := L) (k := k) (A := A.pullback T.hom)
        (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)) := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis (A := A.pullback T.hom)
  intro U c
  rfl

end CompatiblePureFineConstruction.LevelCover

variable {K : Type} [Field K] [CharZero K] {g L k : ℕ} {δ : Fin g → ℕ}
  (M : Pure.Fine.PurePolarizedModel g δ L (Spec (.of K))) [NeZero L] [NeZero k]

def Pure.Fine.PurePolarizedModel.divisorFrameParameter : Over M.space.left :=
  CompatibleLevel.LevelCover.compatibleFullFrameScheme (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level

def Pure.Fine.PurePolarizedModel.divisorFrameLevel :
    (M.universal.abelian.pullback (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)).hom).FullLevel (L * k) :=
  CompatibleLevel.LevelCover.compatibleFullFrameLevel (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level

theorem Pure.Fine.PurePolarizedModel.divisorFrameLevel_compatible :
    (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k)).divisor (L := L) (k := k)
        (A := M.universal.abelian.pullback (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)).hom)
        (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)) =
      M.universal.level.pullback (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)).hom := by
  have h := CompatibleLevel.LevelCover.compatibleFullFrameLevel_compatible (L := L) (N := L * k)
    M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level
  exact (CompatiblePureFineConstruction.LevelCover.divisorLevelTransformation_apply (L := L) (k := k) M.universal.abelian
    (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)) (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k))).symm.trans h

def Pure.Fine.PurePolarizedModel.divisorFramePointsEquiv (T : Over M.space.left) :
    (T ⟶ Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)) ≃
      {β : (M.universal.abelian.pullback T.hom).FullLevel (L * k) |
        β.divisor (L := L) (k := k) (A := M.universal.abelian.pullback T.hom)
            (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)) =
          M.universal.level.pullback T.hom} := by
  refine (CompatibleLevel.LevelCover.compatibleFullFramePointsEquiv (L := L) (N := L * k)
    M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level T).trans
      { toFun := fun β => ⟨β.val,
          (CompatiblePureFineConstruction.LevelCover.divisorLevelTransformation_apply (L := L) (k := k) M.universal.abelian T β.val).symm.trans β.property⟩
        invFun := fun β => ⟨β.val,
          (CompatiblePureFineConstruction.LevelCover.divisorLevelTransformation_apply (L := L) (k := k) M.universal.abelian T β.val).trans β.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

theorem Pure.Fine.PurePolarizedModel.divisorFrameLevel_restrict {T : Over M.space.left}
    (f : T ⟶ Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)) :
    (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k)).restrict (A := M.universal.abelian) f =
      (Pure.Fine.PurePolarizedModel.divisorFramePointsEquiv M T f).val :=
  CompatibleLevel.LevelCover.compatibleFullFrameLevel_restrict (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level f

def Pure.Fine.PurePolarizedModel.divisorLevelSpace : Over (Spec (.of K)) := (Over.map M.space.hom).obj (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k))

def Pure.Fine.PurePolarizedModel.divisorLevelFamily : Level.Data.AddedFullLevel g δ L (L * k) (Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k)).left :=
  Pure.RelativeLevelIso.relativeAddedLevel (L := L) (N := L * k) M.universal (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k))
    (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k))

def Pure.Fine.PurePolarizedModel.divisorLevelModel : Pure.Fine.PurePolarizedModel g δ (L * k) (Spec (.of K)) :=
  ⟨Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k), (Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).forgetAuxiliary⟩

def Pure.Fine.PurePolarizedModel.divisorLevelToAdded : Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k) ⟶ M.addedLevelSpace (N := L * k) :=
  (Over.map M.space.hom).map (CompatibleLevel.LevelCover.compatibleFullFrameInclusion (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level)

instance Pure.Fine.PurePolarizedModel.divisorLevelToAdded_mono : Mono (Pure.Fine.PurePolarizedModel.divisorLevelToAdded M (k := k)) := by
  have h := (CompatibleLevel.LevelCover.compatibleFullFrameInclusion_open_closed (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level).1
  let : IsOpenImmersion (CompatibleLevel.LevelCover.compatibleFullFrameInclusion (L := L) (N := L * k) M.universal.abelian M.space.hom
    (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level).left := h
  have : Mono (Pure.Fine.PurePolarizedModel.divisorLevelToAdded M (k := k)).left :=
    inferInstanceAs (Mono (CompatibleLevel.LevelCover.compatibleFullFrameInclusion (L := L) (N := L * k) M.universal.abelian M.space.hom
      (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level).left)
  exact Over.mono_of_mono_left _

theorem Pure.Fine.PurePolarizedModel.divisorLevelFamily_compatible :
    (Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).prescribed.divisor (L := L) (k := k)
        (A := M.universal.abelian.pullback (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)).hom)
        (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)) =
      (Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).auxiliary.level :=
  Pure.Fine.PurePolarizedModel.divisorFrameLevel_compatible M

def Pure.Fine.PurePolarizedModel.divisorLevelFamilyRecovery :
    Level.Data.AddedFullLevel.Iso ((M.addedLevelUniversal (N := L * k)).pullback (Pure.Fine.PurePolarizedModel.divisorLevelToAdded M).left)
      (Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)) :=
  Pure.RelativeLevelIso.relativeAddedLevelIso (L := L) (N := L * k) M.universal
    (CompatibleLevel.LevelCover.compatibleFullFrameInclusion (L := L) (N := L * k) M.universal.abelian M.space.hom
      (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level)
    (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel (N := L * k) M.universal.abelian M.space.hom)

def Pure.Fine.PurePolarizedModel.divisorLevelFamilyRecoveryAt {T : Over (Spec (.of K))} (f : T ⟶ Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k)) :
    Level.Data.AddedFullLevel.Iso ((M.addedLevelUniversal (N := L * k)).pullback (f ≫ Pure.Fine.PurePolarizedModel.divisorLevelToAdded M).left)
      ((Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).pullback f.left) :=
  (Level.Data.AddedFullLevel.pullbackCompIso (M.addedLevelUniversal (N := L * k))
    (Pure.Fine.PurePolarizedModel.divisorLevelToAdded M).left f.left).symm.trans ((Pure.Fine.PurePolarizedModel.divisorLevelFamilyRecovery M).pullback f.left)

theorem Pure.Fine.PurePolarizedModel.divisorFrame_classifying_exists {T : Over (Spec (.of K))}
    (f : T ⟶ M.space)
    (β : (M.universal.abelian.pullback f.left).FullLevel (L * k))
    (hβ : β.divisor (L := L) (k := k) (A := M.universal.abelian.pullback f.left)
      (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)) =
        M.universal.level.pullback f.left) :
    ∃ v : T ⟶ Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k),
      Nonempty (Level.Data.AddedFullLevel.Iso ((Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).pullback v.left)
        (Pure.RelativeLevelIso.relativeAddedLevel (L := L) (N := L * k) M.universal (Over.mk f.left) β)) := by
  let E := Pure.Fine.PurePolarizedModel.divisorFramePointsEquiv M (k := k) (Over.mk f.left)
  let c := E.symm ⟨β, hβ⟩
  have hc : (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k)).restrict
        (A := M.universal.abelian) c = β :=
    (Pure.Fine.PurePolarizedModel.divisorFrameLevel_restrict M c).trans
        (congrArg Subtype.val (E.apply_symm_apply ⟨β, hβ⟩))
  let v : T ⟶ Pure.Fine.PurePolarizedModel.divisorLevelSpace M (k := k) := Over.homMk c.left (by
    exact (Category.assoc c.left (Pure.Fine.PurePolarizedModel.divisorFrameParameter M (k := k)).hom M.space.hom).symm.trans
      ((congrArg (fun z => z ≫ M.space.hom) c.w).trans f.w))
  have ev : Level.Data.AddedFullLevel.Iso ((Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).pullback v.left)
      (Pure.RelativeLevelIso.relativeAddedLevel (L := L) (N := L * k) M.universal (Over.mk f.left) β) := by
    have ee := Pure.RelativeLevelIso.relativeAddedLevelIso (L := L) (N := L * k) M.universal c
      (Pure.Fine.PurePolarizedModel.divisorFrameLevel M (k := k))
    exact hc ▸ ee
  exact ⟨v, ⟨ev⟩⟩

theorem Pure.Fine.PurePolarizedModel.divisorLevelModel_classifying_exists (hM : M.IsFine)
    (T : Over (Spec (.of K))) (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ (L * k) T.left) :
    ∃ f : T ⟶ (Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).space,
      Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).universal.pullback f.left) B) := by
  let hL := Nat.pos_of_ne_zero (NeZero.ne L)
  let hk := Nat.pos_of_ne_zero (NeZero.ne k)
  let C := Level.Data.AddedFullLevel.ofDivisor hL hk B
  obtain ⟨f, ⟨e⟩, _⟩ := hM T C.auxiliary
  let C' := Level.Data.AddedFullLevel.fromAuxiliaryIso C (M.universal.pullback f.left) e
  let β : (M.universal.abelian.pullback f.left).FullLevel (L * k) :=
    C'.prescribed
  let e' : Level.Data.AddedFullLevel.Iso
      (Pure.RelativeLevelIso.relativeAddedLevel (L := L) (N := L * k) M.universal (Over.mk f.left) β) C :=
    Level.Data.AddedFullLevel.fromAuxiliaryIso_iso C (M.universal.pullback f.left) e
  have hβ : β.divisor (L := L) (k := k) (A := M.universal.abelian.pullback f.left) hL hk =
      M.universal.level.pullback f.left :=
    Level.Data.AddedFullLevel.divisor_compatible_of_iso (L := L) (k := k) hL hk e' rfl
  obtain ⟨v, ⟨ev⟩⟩ := Pure.Fine.PurePolarizedModel.divisorFrame_classifying_exists M (k := k) f β hβ
  exact ⟨v, ⟨(ev.trans e').forgetAuxiliary⟩⟩

variable [Countable K] [LocallyOfFiniteType M.space.hom]

theorem Pure.Fine.PurePolarizedModel.divisorLevelModel_classifying_unique (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ (L * k) T.left)
    (f h : T ⟶ (Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).space)
    (a : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).universal.pullback f.left) B)
    (b : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).universal.pullback h.left) B) : f = h := by
  let hLp := Nat.pos_of_ne_zero (NeZero.ne L)
  let hk := Nat.pos_of_ne_zero (NeZero.ne k)
  let C := Level.Data.AddedFullLevel.ofDivisor hLp hk B
  let a' : Level.Data.AddedFullLevel.Iso ((Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).pullback f.left) C :=
    Level.Data.AddedFullLevel.isoOfDivisorCompatible hLp hk
      (Level.Data.AddedFullLevel.divisor_compatible_pullback hLp hk _ (Pure.Fine.PurePolarizedModel.divisorLevelFamily_compatible M) f.left) rfl a
  let b' : Level.Data.AddedFullLevel.Iso ((Pure.Fine.PurePolarizedModel.divisorLevelFamily M (k := k)).pullback h.left) C :=
    Level.Data.AddedFullLevel.isoOfDivisorCompatible hLp hk
      (Level.Data.AddedFullLevel.divisor_compatible_pullback hLp hk _ (Pure.Fine.PurePolarizedModel.divisorLevelFamily_compatible M) h.left) rfl b
  apply (cancel_mono (Pure.Fine.PurePolarizedModel.divisorLevelToAdded M (k := k))).mp
  exact M.addedLevel_classifying_unique hM hL T C _ _
    ((Pure.Fine.PurePolarizedModel.divisorLevelFamilyRecoveryAt M f).trans a') ((Pure.Fine.PurePolarizedModel.divisorLevelFamilyRecoveryAt M h).trans b')

theorem Pure.Fine.PurePolarizedModel.divisorLevelModel_isFine (hM : M.IsFine) (hL : 3 ≤ L) :
    (Pure.Fine.PurePolarizedModel.divisorLevelModel M (k := k)).IsFine := by
  intro T B
  obtain ⟨f, ⟨a⟩⟩ := Pure.Fine.PurePolarizedModel.divisorLevelModel_classifying_exists M hM T B
  refine ⟨f, ⟨a⟩, ?_⟩
  rintro h ⟨b⟩
  exact Pure.Fine.PurePolarizedModel.divisorLevelModel_classifying_unique M hM hL T B h f b a

omit [LocallyOfFiniteType M.space.hom] in
theorem Pure.Fine.PurePolarizedModel.exists_quasiProjective_fine_pure_model_at_multiple
    (hM : M.IsFine) (hL : 3 ≤ L) (P : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) :
    ∃ F : Pure.Fine.PurePolarizedModel g δ (L * k) (Spec (.of K)),
      F.IsFine ∧ Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation F.space) := by
  have : LocallyOfFiniteType M.space.hom := P.locallyFiniteType
  exact ⟨Pure.Fine.PurePolarizedModel.divisorLevelModel M, Pure.Fine.PurePolarizedModel.divisorLevelModel_isFine M hM hL,
    CompatibleLevel.LevelCover.compatibleFullFrame_quasiProjective (L := L) (N := L * k) M.universal.abelian M.space.hom
      (DivisorLevelInt.LevelCover.divisorLevelTransformation M.universal.abelian (L := L) (k := k)) M.universal.level P⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
