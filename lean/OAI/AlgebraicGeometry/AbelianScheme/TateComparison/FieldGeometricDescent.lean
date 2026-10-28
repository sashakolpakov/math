import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChangeReduced
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Field Geometric Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldGeometricDescent

noncomputable section

/-! Effective descent across an arbitrary characteristic-zero field
extension from compatibility on actual geometric points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {k L : Type u} [Field k] [CharZero k] [Field L]
  (p : Spec (.of L) ⟶ Spec (.of k)) (A B : Over (Spec (.of k)))

abbrev fieldSource : Over (Spec (.of k)) :=
  Over.mk (pullback.fst A.hom p ≫ A.hom)

def fieldSourceProjection : fieldSource p A ⟶ A := Over.homMk (pullback.fst A.hom p) rfl

theorem fieldGeometricDescent [IsIntegral (pullback A.hom p)] [IsSeparated B.hom]
    (ν : fieldSource p A ⟶ B)
    (hν : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ Spec (.of k)) (x y : Over.mk b ⟶ fieldSource p A),
      x ≫ fieldSourceProjection p A = y ≫ fieldSourceProjection p A → x ≫ ν = y ≫ ν) :
    ∃! d : A ⟶ B, fieldSourceProjection p A ≫ d = ν := by
  have : Flat p := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) φ.hom
  have : Surjective p := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact p := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  let U := fieldSource p A
  let π := fieldSourceProjection p A
  have : IsIntegral U.left := inferInstanceAs (IsIntegral (pullback A.hom p))
  let R : Over (Spec (.of k)) := Over.mk (pullback.fst π.left π.left ≫ U.hom)
  have : IsReduced (pullback (π.left ≫ A.hom) p) := FieldBaseChangeReduced.charZero_fieldBaseChange_reduced U.hom p
  let e : R.left ≅ pullback (π.left ≫ A.hom) p := pullbackRightPullbackFstIso A.hom p π.left
  have : IsReduced R.left := isReduced_of_isOpenImmersion e.hom
  let r₁ : R ⟶ U := Over.homMk (pullback.fst π.left π.left) rfl
  let r₂ : R ⟶ U := Over.homMk (pullback.snd π.left π.left) (by
    change pullback.snd π.left π.left ≫ U.hom = pullback.fst π.left π.left ≫ U.hom
    rw [← π.w, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hr : r₁ ≫ π = r₂ ≫ π := Over.OverMorphism.ext pullback.condition
  have hpair : r₁ ≫ ν = r₂ ≫ ν := by
    apply GeometricExt.over_hom_ext_geometric
    intro Ω _ _ b z
    apply hν Ω b (z ≫ r₁) (z ≫ r₂)
    exact (Category.assoc z r₁ π).trans
      ((congrArg (fun a => z ≫ a) hr).trans (Category.assoc z r₂ π).symm)
  have hc : ∀ {W : Scheme.{u}} (x y : W ⟶ U.left), x ≫ π.left = y ≫ π.left →
      x ≫ ν.left = y ≫ ν.left := by
    intro W x y hxy
    let t := pullback.lift x y hxy
    have hs : pullback.fst π.left π.left ≫ ν.left = pullback.snd π.left π.left ≫ ν.left :=
      congrArg Over.Hom.left hpair
    have h := congrArg (fun a => t ≫ a) hs
    simpa only [t, Category.assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc] using h
  have : Flat π.left := inferInstanceAs (Flat (pullback.fst A.hom p))
  have : Surjective π.left := inferInstanceAs (Surjective (pullback.fst A.hom p))
  have : QuasiCompact π.left := inferInstanceAs (QuasiCompact (pullback.fst A.hom p))
  let d₀ := EffectiveEpi.desc π.left ν.left hc
  have hd : π.left ≫ d₀ = ν.left := EffectiveEpi.fac _ _ _
  have hb : d₀ ≫ B.hom = A.hom := by
    apply (cancel_epi π.left).mp
    rw [← Category.assoc, hd, ν.w, π.w]
  let d : A ⟶ B := Over.homMk d₀ hb
  refine ⟨d, Over.OverMorphism.ext hd, ?_⟩
  intro e he
  apply Over.OverMorphism.ext
  apply (cancel_epi π.left).mp
  exact (congrArg Over.Hom.left he).trans hd.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldGeometricDescent
