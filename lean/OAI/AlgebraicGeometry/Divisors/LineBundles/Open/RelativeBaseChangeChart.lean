import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap

/-! # Relative Base Change Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelativeBaseChangeChart.BundleCycles

noncomputable section

section

/-! A cartesian open relative chart produces an actual cartesian
open chart after arbitrary change of the base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X V U Y : Scheme.{0}} (p : E ⟶ X) (q : V ⟶ U)
    (i : U ⟶ X) (j : V ⟶ E) (hs : IsPullback q j i p) (b : Y ⟶ X)

def openRelativeBaseChangeChartMap :
    pullback q (pullback.snd b i) ⟶ pullback p b :=
  pullback.lift (pullback.fst q (pullback.snd b i) ≫ j)
    (pullback.snd q (pullback.snd b i) ≫ pullback.fst b i)
    (by rw [Category.assoc, ← hs.w, ← Category.assoc, pullback.condition,
      Category.assoc, ← pullback.condition, ← Category.assoc])

theorem openRelativeBaseChangeChartMap_fst :
    openRelativeBaseChangeChartMap p q i j hs b ≫ pullback.fst p b =
      pullback.fst q (pullback.snd b i) ≫ j := pullback.lift_fst _ _ _

theorem openRelativeBaseChangeChartMap_snd :
    openRelativeBaseChangeChartMap p q i j hs b ≫ pullback.snd p b =
      pullback.snd q (pullback.snd b i) ≫ pullback.fst b i := pullback.lift_snd _ _ _

theorem openRelativeBaseChangeChartMap_isPullback :
    IsPullback (openRelativeBaseChangeChartMap p q i j hs b)
      (pullback.fst q (pullback.snd b i)) (pullback.fst p b) j := by
  have H := (IsPullback.of_hasPullback q (pullback.snd b i)).flip.paste_horiz
    (IsPullback.of_hasPullback b i)
  rw [hs.w] at H
  have H' : IsPullback (openRelativeBaseChangeChartMap p q i j hs b ≫ pullback.snd p b)
      (pullback.fst q (pullback.snd b i)) b (j ≫ p) := by
    rw [openRelativeBaseChangeChartMap_snd]
    exact H
  exact H'.of_right (openRelativeBaseChangeChartMap_fst p q i j hs b)
    (IsPullback.of_hasPullback p b).flip

instance openRelativeBaseChangeChartMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (openRelativeBaseChangeChartMap p q i j hs b) :=
  MorphismProperty.of_isPullback (openRelativeBaseChangeChartMap_isPullback p q i j hs b).flip inferInstance

theorem openRelativeBaseChangeChart_projection_isPullback :
    IsPullback (pullback.snd q (pullback.snd b i))
      (openRelativeBaseChangeChartMap p q i j hs b) (pullback.fst b i) (pullback.snd p b) := by
  have H := (IsPullback.of_hasPullback q (pullback.snd b i)).flip.paste_vert hs
  have H' : IsPullback (pullback.snd q (pullback.snd b i))
      (openRelativeBaseChangeChartMap p q i j hs b ≫ pullback.fst p b)
      (pullback.fst b i ≫ b) p := by
    rw [openRelativeBaseChangeChartMap_fst, pullback.condition]
    exact H
  exact H'.of_bot (openRelativeBaseChangeChartMap_snd p q i j hs b).symm
    (IsPullback.of_hasPullback p b).flip

end

/-! An actual cartesian relative chart whose base map factors through
an open subscheme lifts to the pullback over that open subscheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X V B U : Scheme.{0}} (p : E ⟶ X) (q : V ⟶ B)
    (b : B ⟶ X) (j : V ⟶ E) (hs : IsPullback q j b p)
    (i : U ⟶ X) (a : B ⟶ U) (ha : a ≫ i = b)

def openRelativeChartLift : V ⟶ pullback p i :=
  pullback.lift j (q ≫ a) (by rw [Category.assoc, ha, hs.w])

theorem openRelativeChartLift_fst : openRelativeChartLift p q b j hs i a ha ≫ pullback.fst p i = j :=
  pullback.lift_fst _ _ _

theorem openRelativeChartLift_snd : openRelativeChartLift p q b j hs i a ha ≫ pullback.snd p i = q ≫ a :=
  pullback.lift_snd _ _ _

instance openRelativeChartLift_isOpenImmersion [IsOpenImmersion i] [IsOpenImmersion j] :
    IsOpenImmersion (openRelativeChartLift p q b j hs i a ha) := by
  let : IsOpenImmersion (openRelativeChartLift p q b j hs i a ha ≫ pullback.fst p i) := by
    rw [openRelativeChartLift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst p i)

theorem openRelativeChartLift_isPullback :
    IsPullback q (openRelativeChartLift p q b j hs i a ha) a (pullback.snd p i) := by
  have H : IsPullback q (openRelativeChartLift p q b j hs i a ha ≫ pullback.fst p i) (a ≫ i) p := by
    rw [openRelativeChartLift_fst, ha]
    exact hs
  exact H.of_bot (openRelativeChartLift_snd p q b j hs i a ha).symm (IsPullback.of_hasPullback p i).flip

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelativeBaseChangeChart.BundleCycles
