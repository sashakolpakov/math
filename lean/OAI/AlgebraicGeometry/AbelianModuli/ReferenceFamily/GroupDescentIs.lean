import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Descent Is -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs.GroupDescent

/-! Effective descent preserves the actual group-scheme operations.
Faithfulness of monoidal pullback reflects the two group-map equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Functor.LaxMonoidal
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem isMonHom_of_map {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)] : IsMonHom f where
  one_hom := by
    apply F.map_injective
    apply (cancel_epi (ε F)).mp
    have h := IsMonHom.one_hom (F.map f)
    simpa only [Functor.obj.η_def, Category.assoc, F.map_comp] using h
  mul_hom := by
    apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F X X)).mp
    have h := IsMonHom.mul_hom (F.map f)
    simpa only [Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      F.map_comp] using h

variable {S S' : Scheme.{0}} (u : S' ⟶ S)
  [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
  {X Y : Over S} [GrpObj X] [GrpObj Y]

/-- An overlap-compatible local group isomorphism descends uniquely as
an actual group-scheme isomorphism over the original base. -/
theorem exists_unique_groupIso
    (e : Grp.mk ((Over.pullback u).obj X) ≅ Grp.mk ((Over.pullback u).obj Y))
    (hh : EtaleDescentLocal.EtaleDescent.Compatible u e.hom.hom.hom)
    (hi : EtaleDescentLocal.EtaleDescent.Compatible u e.inv.hom.hom) :
    ∃! q : Grp.mk X ≅ Grp.mk Y,
      (Over.pullback u).mapIso ((Grp.forget (Over S)).mapIso q) =
        (Grp.forget (Over S')).mapIso e := by
  obtain ⟨q, hq, huniq⟩ := EtaleDescentLocal.EtaleDescent.exists_unique_iso u
    ((Grp.forget (Over S')).mapIso e) hh hi
  have he : (Over.pullback u).map q.hom = e.hom.hom.hom := congrArg Iso.hom hq
  have hlocal : IsMonHom ((Over.pullback u).map q.hom) := by
    rw [he]
    exact e.hom.hom.isMonHom_hom
  let : IsMonHom ((Over.pullback u).map q.hom) := hlocal
  let : IsMonHom q.hom := isMonHom_of_map (Over.pullback u) q.hom
  let r := Grp.mkIso' q
  refine ⟨r, hq, ?_⟩
  intro z hz
  apply Iso.ext
  apply Grp.hom_ext
  exact congrArg Iso.hom (huniq ((Grp.forget (Over S)).mapIso z) hz)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs.GroupDescent

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs.GroupBaseChange

/-! Canonical group-compatible base change for arbitrary group schemes.
The pullback adjunction preserves multiplication on actual scheme points.
This generalizes the HilbertConstruction abelian-scheme point calculation to torsion and
constant group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}}

/-- The pullback adjunction identifies points over a changed base. -/
def baseChangePointsEquiv (H : Over S) [GrpObj H] (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (Over.pullback f).obj H) ≃ ((Over.map f).obj T ⟶ H) :=
  ((Over.mapPullbackAdj f).homEquiv T H).symm

@[simp]
theorem baseChangePointsEquiv_apply (H : Over S) [GrpObj H] (f : S' ⟶ S)
    (T : Over S') (x : (T ⟶ (Over.pullback f).obj H)) :
    (baseChangePointsEquiv H f T x).left =
      x.left ≫ Limits.pullback.fst H.hom f := rfl

/-- The base-change identification preserves the group law on points. -/
def baseChangePointsMulEquiv (H : Over S) [GrpObj H] (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (Over.pullback f).obj H) ≃* ((Over.map f).obj T ⟶ H) where
  toEquiv := baseChangePointsEquiv H f T
  map_mul' x y := by
    let F := Over.pullback f
    let p := Limits.pullback.fst H.hom f
    let p₂ := Limits.pullback.fst (H ⊗ H).hom f
    have hμ : μ[(Over.pullback f).obj H].left ≫ p =
        (Functor.LaxMonoidal.μ F H H).left ≫ p₂ ≫ μ[H].left := by
      change (Functor.LaxMonoidal.μ F H H ≫ F.map μ[H]).left ≫ p = _
      simp only [F, p, p₂, Over.comp_left, Over.pullback_map_left,
        Category.assoc, Limits.pullback.lift_fst]
    have hassoc (z : (H ⊗ H).left ⟶ H.left) :
        ((lift x y).left ≫ (Functor.LaxMonoidal.μ F H H).left ≫ p₂) ≫ z =
          (lift x y).left ≫ ((Functor.LaxMonoidal.μ F H H).left ≫ p₂ ≫ z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (lift x y).left ≫ a) (Category.assoc _ _ _))
    have hpair : (lift x y).left ≫ (Functor.LaxMonoidal.μ F H H).left ≫ p₂ =
        (lift (baseChangePointsEquiv H f T x) (baseChangePointsEquiv H f T y)).left := by
      apply Over.tensorObj_ext
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F H H).left ≫ p₂ ≫
                Limits.pullback.fst H.hom H.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.fst ((Over.pullback f).obj H).hom ((Over.pullback f).obj H).hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_fst (f := f) H H)
          _ = x.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.fst ((Over.pullback f).obj H).hom ((Over.pullback f).obj H).hom = x.left by
              simp only [Over.lift_left, Limits.pullback.lift_fst]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_fst, baseChangePointsEquiv_apply, p]
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F H H).left ≫ p₂ ≫
                Limits.pullback.snd H.hom H.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.snd ((Over.pullback f).obj H).hom ((Over.pullback f).obj H).hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_snd (f := f) H H)
          _ = y.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.snd ((Over.pullback f).obj H).hom ((Over.pullback f).obj H).hom = y.left by
              simp only [Over.lift_left, Limits.pullback.lift_snd]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_snd, baseChangePointsEquiv_apply, p]
    apply Over.OverMorphism.ext
    change ((lift x y).left ≫ μ[(Over.pullback f).obj H].left) ≫ p =
      (lift (baseChangePointsEquiv H f T x) (baseChangePointsEquiv H f T y)).left ≫ μ[H].left
    calc
      _ = (lift x y).left ≫ (μ[(Over.pullback f).obj H].left ≫ p) := Category.assoc _ _ _
      _ = (lift x y).left ≫
          ((Functor.LaxMonoidal.μ F H H).left ≫ p₂ ≫ μ[H].left) :=
        congrArg (fun a => (lift x y).left ≫ a) hμ
      _ = ((lift x y).left ≫ (Functor.LaxMonoidal.μ F H H).left ≫ p₂) ≫
          μ[H].left := (hassoc μ[H].left).symm
      _ = _ := congrArg (fun a => a ≫ μ[H].left) hpair

def baseChangeYonedaIso (H : Over S) [GrpObj H] (f : S' ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj H) ≅ (Over.map f).op ⋙ yonedaGrpObj H :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (baseChangePointsMulEquiv H f T.unop)) (by
    intro T U j
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs.GroupBaseChange

end

end OAI
