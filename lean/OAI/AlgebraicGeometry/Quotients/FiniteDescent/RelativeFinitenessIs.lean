import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Relative Finiteness Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFinitenessIs.Construction.RelativeFiniteness

/-!
# Relative finiteness from field base changes

For a proper morphism over a base scheme, finiteness can be checked after
every field-valued base change of the base. This reduces the finiteness of
relative multiplication maps to multiplication on abelian varieties.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem baseChange_isPullback {S T : Scheme.{u}} {X Y : Over S}
    (a : T ⟶ S) (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom a) ((Over.pullback a).map f).left
      f.left (pullback.fst Y.hom a) := by
  have he : ((Over.pullback a).map f).left ≫ pullback.snd Y.hom a = pullback.snd X.hom a :=
    pullback.lift_snd _ _ _
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback Y.hom a)
  · simpa only [he, Category.assoc, Over.w] using IsPullback.of_hasPullback X.hom a
  · exact (pullback.lift_fst _ _ _).symm

/-- Properness lets finiteness descend from any surjective base change:
the finite fibers upstairs map onto the fibers downstairs. -/
theorem finite_of_surjective_baseChange {S T : Scheme.{u}} {X Y : Over S}
    (a : T ⟶ S) [Surjective a] (f : X ⟶ Y) [IsProper f.left]
    [IsFinite ((Over.pullback a).map f).left] : IsFinite f.left := by
  have : LocallyQuasiFinite f.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    obtain ⟨y', hy'⟩ := (pullback.fst Y.hom a).surjective y
    have hf := (((Over.pullback a).map f).left.finite_preimage_singleton y').image
      (pullback.fst X.hom a)
    rw [Scheme.image_preimage_eq_of_isPullback (baseChange_isPullback a f).flip,
      Set.image_singleton, hy'] at hf
    exact hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

theorem finite_of_field_baseChanges {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsProper f.left]
    (h : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      IsFinite ((Over.pullback a).map f).left) : IsFinite f.left := by
  have : LocallyQuasiFinite f.left := by
    apply LocallyQuasiFinite.of_fiberToSpecResidueField
    intro y
    let p := Y.left.fromSpecResidueField y
    let a := p ≫ Y.hom
    let g : Spec (Y.left.residueField y) ⟶ pullback Y.hom a :=
      pullback.lift p (𝟙 _) (by simp [a])
    have hg : g ≫ pullback.fst Y.hom a = p := pullback.lift_fst _ _ _
    let fp := ((Over.pullback a).map f).left
    have : IsFinite fp := h (Y.left.residueField y) a
    let hp := baseChange_isPullback a f
    let r : pullback f.left p ⟶ pullback X.hom a :=
      hp.lift (pullback.fst f.left p) (pullback.snd f.left p ≫ g) (by
        rw [Category.assoc, hg, pullback.condition])
    have hpr : IsPullback r (pullback.snd f.left p) fp g := by
      apply IsPullback.of_right (t := hp)
      · simpa only [r, IsPullback.lift_fst, hg] using IsPullback.of_hasPullback f.left p
      · exact hp.lift_snd _ _ _
    have : IsFinite (f.left.fiberToSpecResidueField y) :=
      MorphismProperty.of_isPullback hpr inferInstance
    infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

theorem power_isProper {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsProper A.hom] (n : ℕ) :
    IsProper ((𝟙 A : A ⟶ A) ^ n).left := by
  have : IsProper (((𝟙 A : A ⟶ A) ^ n).left ≫ A.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ A.hom

/-- Finiteness of multiplication on all field base changes implies
finiteness of the relative multiplication morphism. -/
theorem finite_power_of_field_powers {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsProper A.hom] (n : ℕ)
    (h : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      let B := (Over.pullback a).obj A
      letI : GrpObj B := Functor.grpObjObj
      IsFinite ((𝟙 B : B ⟶ B) ^ n).left) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have := power_isProper A n
  apply finite_of_field_baseChanges
  intro K hK a
  let F := Over.pullback a
  let B := F.obj A
  let : GrpObj B := Functor.grpObjObj
  have he : F.map ((𝟙 A : A ⟶ A) ^ n) = (𝟙 B : B ⟶ B) ^ n := by
    exact ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun k => k ^ n) (F.map_id A))
  change IsFinite (F.map ((𝟙 A : A ⟶ A) ^ n)).left
  rw [he]
  exact h K a

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFinitenessIs.Construction.RelativeFiniteness
