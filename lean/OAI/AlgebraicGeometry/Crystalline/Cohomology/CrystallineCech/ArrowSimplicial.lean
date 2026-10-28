import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowTuples
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FiberTuple

/-! # Arrow Simplicial -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial

noncomputable section

/-!
# The simplicial identification of native Čech arrows

Native arrows into principal intersections form a simplicial set.
The tuple equivalence preserves every simplicial map: the base arrow is
unchanged, the tuple indices are precomposed, and monicity identifies the
remaining lift data. This supplies an isomorphism of the actual diagrams.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q T : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

def Arrows (n : SimplexCategoryᵒᵖ) :=
  Σ t : ((N).obj n).I, T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj t)

def base (n : SimplexCategoryᵒᵖ) (z : Arrows p k X Q T s n) : T ⟶ Q :=
  z.2 ≫ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (((N).obj n).obj z.1)

def map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    Arrows p k X Q T s n → Arrows p k X Q T s m :=
  fun z => ⟨((N).map f).f z.1,
    z.2 ≫ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q (((N).map f).φ z.1)⟩

theorem map_base {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (z : Arrows p k X Q T s n) :
    base p k X Q T s m (CrystallineCechArrowSimplicial.map p k X Q T s f z) = base p k X Q T s n z :=
  (Category.assoc _ _ _).trans (congrArg (fun a => z.2 ≫ a)
    (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q (((N).map f).φ z.1)))

def simplicial : SimplicialObject (Type u) where
  obj n := Arrows p k X Q T s n
  map f := ↾(CrystallineCechArrowSimplicial.map p k X Q T s f)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply (cancel_mono (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (((N).obj n).obj z.1))).mp
    exact map_base p k X Q T s (𝟙 n) z
  map_comp {n m l} f g := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply (cancel_mono (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q
      (((N).obj l).obj (CrystallineCechArrowSimplicial.map p k X Q T s g (CrystallineCechArrowSimplicial.map p k X Q T s f z)).1))).mp
    exact (map_base p k X Q T s (f ≫ g) z).trans
      ((map_base p k X Q T s g (CrystallineCechArrowSimplicial.map p k X Q T s f z)).trans (map_base p k X Q T s f z)).symm

theorem liftIndex_heq {q q' : T ⟶ Q} (h : q = q')
    (a : ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s q)
    (b : ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s q') (hab : a.1 = b.1) : HEq a b := by
  cases h
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp at hab
  cases hab
  exact heq_of_eq (congrArg (fun f => Sigma.mk i f) (Subsingleton.elim a b))

theorem tuple_heq {β : Type v} {q q' : T ⟶ Q} (h : q = q')
    (a : β → ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s q)
    (b : β → ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s q')
    (hab : ∀ l, (a l).1 = (b l).1) : HEq a b := by
  cases h
  apply heq_of_eq
  funext l
  exact eq_of_heq (liftIndex_heq p k X Q T s rfl (a l) (b l) (hab l))

def iso : simplicial p k X Q T s ≅
    FiberTuple.FiberTupleCech.nerve (ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s) :=
  NatIso.ofComponents
    (fun n => Equiv.toIso (ArrowTuples.CrystallineCechArrowTuples.equiv p k X Q T s n.unop.len))
    (by
      intro n m f
      apply ConcreteCategory.hom_ext
      intro z
      refine Sigma.ext (map_base p k X Q T s f z) ?_
      exact tuple_heq p k X Q T s (map_base p k X Q T s f z) _ _ (fun _ => rfl))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial
