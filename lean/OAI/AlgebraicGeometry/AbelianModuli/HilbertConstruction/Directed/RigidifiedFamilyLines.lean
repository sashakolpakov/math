import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.NormalizedLineOpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedFamilyPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons

/-! # Rigidified Family Lines -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines

noncomputable section

/-! A directed system of normalized family lines has canonical
comparisons on every actual intersection. Pairwise existence is proved
by the directed intersection cover; all cocycles and pullback equations
then follow from uniqueness of normalized line isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

structure DirectedRigidifiedFamilyLines {S : Scheme.{0}} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (E : Over S) (C : E.left.OpenCover.{0})
    [Category C.I₀] [C.LocallyDirected] where
  line : ∀ i, RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A (Embedded.FamilyOpenCover.overOpenCoverObject E C i)).left
  transition : ∀ {i j : C.I₀} (f : i ⟶ j),
    Line.Bundles.LineBundle.pullbackClass (Embedded.CoverComparisons.overOpenCoverTransition E C f ▷ A.scheme).left
      (Line.Bundles.LineBundle.classOf (line j).lineBundle) = Line.Bundles.LineBundle.classOf (line i).lineBundle

namespace DirectedRigidifiedFamilyLines
variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  {A : Abelian.Schemes.AbelianScheme g S} {E : Over S} {C : E.left.OpenCover.{0}}
  [Category C.I₀] [C.LocallyDirected] (D : DirectedRigidifiedFamilyLines A E C)

omit [IsLocallyNoetherian S] in
private theorem familyClass_comp {T U V : Over S} (a : U ⟶ T) (b : T ⟶ V)
    (q : Line.Bundles.LineBundle.IsoClass (V ⊗ A.scheme).left) :
    Line.Bundles.LineBundle.pullbackClass (a ▷ A.scheme).left
        (Line.Bundles.LineBundle.pullbackClass (b ▷ A.scheme).left q) =
      Line.Bundles.LineBundle.pullbackClass ((a ≫ b) ▷ A.scheme).left q :=
  (Line.Bundles.LineBundle.pullbackClass_comp (a ▷ A.scheme).left (b ▷ A.scheme).left q).symm.trans
    (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (comp_whiskerRight a b A.scheme).symm))

def pairTest (i j : C.I₀) : Over S :=
  Over.mk (pullback.fst (C.f i) (C.f j) ≫ (C.f i ≫ E.hom))

def pairFirst (i j : C.I₀) : pairTest (E := E) i j ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i :=
  Over.homMk (pullback.fst (C.f i) (C.f j)) rfl

def pairSecond (i j : C.I₀) : pairTest (E := E) i j ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j :=
  Over.homMk (pullback.snd (C.f i) (C.f j)) (by
    change pullback.snd (C.f i) (C.f j) ≫ (C.f j ≫ E.hom) =
      pullback.fst (C.f i) (C.f j) ≫ (C.f i ≫ E.hom)
    rw [← Category.assoc, ← pullback.condition, Category.assoc])

def pairRefinementMap (i j : C.I₀) (k : (C.intersectionOfLocallyDirected i j).I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject (pairTest (E := E) i j) (C.intersectionOfLocallyDirected i j) k ⟶
      Embedded.FamilyOpenCover.overOpenCoverObject E C k.1 :=
  Over.homMk (𝟙 (C.X k.1)) (by
    change 𝟙 (C.X k.1) ≫ (C.f k.1 ≫ E.hom) =
      pullback.lift (C.trans k.2.1) (C.trans k.2.2) _ ≫
        (pullback.fst (C.f i) (C.f j) ≫ (C.f i ≫ E.hom))
    rw [Category.id_comp, ← Category.assoc, pullback.lift_fst,
      ← Category.assoc, C.trans_map])

omit [IsLocallyNoetherian S] in
theorem pairRefinement_first (i j : C.I₀) (k : (C.intersectionOfLocallyDirected i j).I₀) :
    Embedded.FamilyOpenCover.overOpenCoverMap (pairTest (E := E) i j) (C.intersectionOfLocallyDirected i j) k ≫ pairFirst i j =
      pairRefinementMap (E := E) i j k ≫ Embedded.CoverComparisons.overOpenCoverTransition E C k.2.1 := by
  apply Over.OverMorphism.ext
  exact (pullback.lift_fst (C.trans k.2.1) (C.trans k.2.2) _).trans
    (Category.id_comp _).symm

omit [IsLocallyNoetherian S] in
theorem pairRefinement_second (i j : C.I₀) (k : (C.intersectionOfLocallyDirected i j).I₀) :
    Embedded.FamilyOpenCover.overOpenCoverMap (pairTest (E := E) i j) (C.intersectionOfLocallyDirected i j) k ≫ pairSecond i j =
      pairRefinementMap (E := E) i j k ≫ Embedded.CoverComparisons.overOpenCoverTransition E C k.2.2 := by
  apply Over.OverMorphism.ext
  exact (pullback.lift_snd (C.trans k.2.1) (C.trans k.2.2) _).trans
    (Category.id_comp _).symm

/-- This uses the actual common-refinement cover of the intersection.
The raw class equality on each member is supplied by the two original
transition equations. -/
theorem pairClass (i j : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass (pairFirst (E := E) i j ▷ A.scheme).left
        (Line.Bundles.LineBundle.classOf (D.line i).lineBundle) =
      Line.Bundles.LineBundle.pullbackClass (pairSecond (E := E) i j ▷ A.scheme).left
        (Line.Bundles.LineBundle.classOf (D.line j).lineBundle) := by
  let Li := (D.line i).familyPullback A (pairFirst (E := E) i j)
  let Lj := (D.line j).familyPullback A (pairSecond (E := E) i j)
  apply Quotient.sound
  apply A.normalizedLineIso_of_openCover (pairTest (E := E) i j)
    Li.lineBundle Lj.lineBundle Li.rigidification Lj.rigidification
    (C.intersectionOfLocallyDirected i j)
  intro k
  let r := pairRefinementMap (E := E) i j k
  let t := Embedded.FamilyOpenCover.overOpenCoverMap (pairTest (E := E) i j) (C.intersectionOfLocallyDirected i j) k
  let a := pairFirst (E := E) i j
  let b := pairSecond (E := E) i j
  have hi : Line.Bundles.LineBundle.pullbackClass (t ▷ A.scheme).left
        (Line.Bundles.LineBundle.pullbackClass (a ▷ A.scheme).left (Line.Bundles.LineBundle.classOf (D.line i).lineBundle)) =
      Line.Bundles.LineBundle.pullbackClass (r ▷ A.scheme).left (Line.Bundles.LineBundle.classOf (D.line k.1).lineBundle) :=
    (familyClass_comp t a _).trans
      ((congrArg (fun q => Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left
        (Line.Bundles.LineBundle.classOf (D.line i).lineBundle)) (pairRefinement_first (E := E) i j k)).trans
        ((familyClass_comp r (Embedded.CoverComparisons.overOpenCoverTransition E C k.2.1) _).symm.trans
          (congrArg (Line.Bundles.LineBundle.pullbackClass (r ▷ A.scheme).left) (D.transition k.2.1))))
  have hj : Line.Bundles.LineBundle.pullbackClass (t ▷ A.scheme).left
        (Line.Bundles.LineBundle.pullbackClass (b ▷ A.scheme).left (Line.Bundles.LineBundle.classOf (D.line j).lineBundle)) =
      Line.Bundles.LineBundle.pullbackClass (r ▷ A.scheme).left (Line.Bundles.LineBundle.classOf (D.line k.1).lineBundle) :=
    (familyClass_comp t b _).trans
      ((congrArg (fun q => Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left
        (Line.Bundles.LineBundle.classOf (D.line j).lineBundle)) (pairRefinement_second (E := E) i j k)).trans
        ((familyClass_comp r (Embedded.CoverComparisons.overOpenCoverTransition E C k.2.2) _).symm.trans
          (congrArg (Line.Bundles.LineBundle.pullbackClass (r ▷ A.scheme).left) (D.transition k.2.2))))
  exact hi.trans hj.symm

def pairLift {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) : T ⟶ pairTest (E := E) i j := by
  let α : T.left ⟶ C.X i := a.left
  let β : T.left ⟶ C.X j := b.left
  have hαβ : α ≫ C.f i = β ≫ C.f j := congrArg Over.Hom.left h
  let q : T.left ⟶ pullback (C.f i) (C.f j) := pullback.lift α β hαβ
  exact Over.homMk q ((Category.assoc q (pullback.fst (C.f i) (C.f j))
    (C.f i ≫ E.hom)).symm.trans
      ((congrArg (fun k => k ≫ (C.f i ≫ E.hom)) (pullback.lift_fst α β hαβ)).trans a.w))

omit [IsLocallyNoetherian S] [Category C.I₀] [C.LocallyDirected] in
theorem pairLift_first {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) :
    pairLift i j a b h ≫ pairFirst i j = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

omit [IsLocallyNoetherian S] [Category C.I₀] [C.LocallyDirected] in
theorem pairLift_second {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) :
    pairLift i j a b h ≫ pairSecond i j = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

theorem class_eq {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) :
    Line.Bundles.LineBundle.classOf ((D.line i).familyPullback A a).lineBundle =
      Line.Bundles.LineBundle.classOf ((D.line j).familyPullback A b).lineBundle := by
  let t := pairLift i j a b h
  have hi := familyClass_comp t (pairFirst (E := E) i j) (Line.Bundles.LineBundle.classOf (D.line i).lineBundle)
  have hj := familyClass_comp t (pairSecond (E := E) i j) (Line.Bundles.LineBundle.classOf (D.line j).lineBundle)
  rw [pairLift_first] at hi
  rw [pairLift_second] at hj
  exact hi.symm.trans ((congrArg (Line.Bundles.LineBundle.pullbackClass (t ▷ A.scheme).left) (D.pairClass i j)).trans hj)

/-- Canonical normalized comparison on every test of an overlap. -/
def comparison {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) :
    RigidifiedLineBundles.RigidifiedLineBundleIso ((D.line i).familyPullback A a) ((D.line j).familyPullback A b) :=
  A.rigidifiedProductComparison T _ _ (Quotient.exact (D.class_eq i j a b h))

theorem comparison_self {T : Over S} (i : C.I₀) (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) :
    D.comparison i i a a rfl = RigidifiedLineBundles.RigidifiedLineBundleIso.refl _ := by
  let : Subsingleton (RigidifiedLineBundles.RigidifiedLineBundleIso ((D.line i).familyPullback A a)
      ((D.line i).familyPullback A a)) :=
    RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
      (A.familyZero_globalFunctions_bijective T).1 _ _
  exact Subsingleton.elim _ _

theorem comparison_comp {T : Over S} (i j k : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (c : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C k)
    (hab : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j)
    (hbc : b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j = c ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C k) :
    (D.comparison i j a b hab).trans (D.comparison j k b c hbc) =
      D.comparison i k a c (hab.trans hbc) := by
  let : Subsingleton (RigidifiedLineBundles.RigidifiedLineBundleIso ((D.line i).familyPullback A a)
      ((D.line k).familyPullback A c)) :=
    RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
      (A.familyZero_globalFunctions_bijective T).1 _ _
  exact Subsingleton.elim _ _

theorem comparison_natural {T U : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j)
    (t : U ⟶ T) (a' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C i) (b' : U ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E C j)
    (ha : t ≫ a = a') (hb : t ≫ b = b')
    (h' : a' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C i = b' ≫ Embedded.FamilyOpenCover.overOpenCoverMap E C j) :
    (D.comparison i j a b h).familyPullbackTo A a b t a' b' ha hb = D.comparison i j a' b' h' := by
  let : Subsingleton (RigidifiedLineBundles.RigidifiedLineBundleIso ((D.line i).familyPullback A a')
      ((D.line j).familyPullback A b')) :=
    RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left
      (A.familyZero_globalFunctions_bijective U).1 _ _
  exact Subsingleton.elim _ _

end DirectedRigidifiedFamilyLines

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines
