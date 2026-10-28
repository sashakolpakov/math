import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftCocycle
import Mathlib.AlgebraicGeometry.Gluing

/-! # Lift Glue Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale

noncomputable section

/-! The actual scheme glue datum for a family of nilpotent etale
chart lifts. Its cocycle is proved from the constructed transitions. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} {i : X₀ ⟶ X} {f₀ : Y₀ ⟶ X₀}
  (A B C : LiftOverlap.Chart i f₀)

abbrev LiftOverlap.Chart.triple := pullback (A.overlap B).ι (A.overlap C).ι

theorem LiftOverlap.Chart.triple_range :
    Set.range (pullback.fst (A.overlap B).ι (A.overlap C).ι ≫ A.transition B) ⊆
      Set.range (B.overlap C).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  apply (B.mem_overlap_iff C _).2
  change B.point (A.transition B ((pullback.fst (A.overlap B).ι (A.overlap C).ι) z)) ∈ _
  rw [LiftOverlap.Chart.point_transition]
  have he := congrArg (fun q : A.triple B C ⟶ A.scheme => q z)
    (pullback.condition (f := (A.overlap B).ι) (g := (A.overlap C).ι))
  change (A.overlap B).ι ((pullback.fst (A.overlap B).ι (A.overlap C).ι) z) =
    (A.overlap C).ι ((pullback.snd (A.overlap B).ι (A.overlap C).ι) z) at he
  rw [he]
  exact (A.mem_overlap_iff C _).1 ((pullback.snd (A.overlap B).ι (A.overlap C).ι z).2)

def LiftOverlap.Chart.tripleFirst : A.triple B C ⟶ (B.overlap C).toScheme :=
  IsOpenImmersion.lift (B.overlap C).ι
    (pullback.fst (A.overlap B).ι (A.overlap C).ι ≫ A.transition B) (A.triple_range B C)

@[reassoc] theorem LiftOverlap.Chart.tripleFirst_ι : A.tripleFirst B C ≫ (B.overlap C).ι =
    pullback.fst (A.overlap B).ι (A.overlap C).ι ≫ A.transition B :=
  IsOpenImmersion.lift_fac _ _ _

theorem LiftOverlap.Chart.tripleFirst_transition : A.tripleFirst B C ≫ B.transition C =
    pullback.snd (A.overlap B).ι (A.overlap C).ι ≫ A.transition C :=
  A.composition B C (pullback.fst _ _) (A.tripleFirst B C) (pullback.snd _ _)
    (A.tripleFirst_ι B C).symm pullback.condition

def LiftOverlap.Chart.tripleMap : A.triple B C ⟶ B.triple C A :=
  pullback.lift (A.tripleFirst B C)
    (pullback.fst (A.overlap B).ι (A.overlap C).ι ≫ A.transitionOpen B)
    (by rw [LiftOverlap.Chart.tripleFirst_ι, Category.assoc, LiftOverlap.Chart.transitionOpen_ι])

@[reassoc] theorem LiftOverlap.Chart.tripleMap_fst : A.tripleMap B C ≫ pullback.fst _ _ = A.tripleFirst B C :=
  pullback.lift_fst _ _ _

@[reassoc] theorem LiftOverlap.Chart.tripleMap_snd : A.tripleMap B C ≫ pullback.snd _ _ =
    pullback.fst (A.overlap B).ι (A.overlap C).ι ≫ A.transitionOpen B :=
  pullback.lift_snd _ _ _

@[reassoc] theorem LiftOverlap.Chart.tripleMap_tripleFirst : A.tripleMap B C ≫ B.tripleFirst C A =
    pullback.snd (A.overlap B).ι (A.overlap C).ι ≫ A.transitionOpen C := by
  apply (cancel_mono (C.overlap A).ι).mp
  rw [Category.assoc, LiftOverlap.Chart.tripleFirst_ι, ← Category.assoc, LiftOverlap.Chart.tripleMap_fst,
    LiftOverlap.Chart.tripleFirst_transition, Category.assoc, LiftOverlap.Chart.transitionOpen_ι]

theorem LiftOverlap.Chart.tripleMap_cocycle : A.tripleMap B C ≫ B.tripleMap C A ≫ C.tripleMap A B = 𝟙 _ := by
  apply (cancel_mono (pullback.snd (A.overlap B).ι (A.overlap C).ι)).mp
  simp only [Category.assoc, LiftOverlap.Chart.tripleMap_snd, LiftOverlap.Chart.tripleMap_fst_assoc, Category.id_comp]
  rw [← Category.assoc, LiftOverlap.Chart.tripleMap_tripleFirst, Category.assoc,
    LiftOverlap.Chart.transitionOpen_inv, Category.comp_id]

def LiftOverlap.Chart.glueData {J : Type u} (D : J → LiftOverlap.Chart i f₀) : Scheme.GlueData where
  J := J
  U a := (D a).scheme
  V ab := ((D ab.1).overlap (D ab.2)).toScheme
  f a b := ((D a).overlap (D b)).ι
  f_id a := by
    rw [(D a).overlap_self]
    exact (Scheme.topIso (D a).scheme).isIso_hom
  t a b := (D a).transitionOpen (D b)
  t_id a := (D a).transitionOpen_self
  t' a b c := (D a).tripleMap (D b) (D c)
  t_fac a b c := (D a).tripleMap_snd (D b) (D c)
  cocycle a b c := (D a).tripleMap_cocycle (D b) (D c)
  f_open a b := inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale
