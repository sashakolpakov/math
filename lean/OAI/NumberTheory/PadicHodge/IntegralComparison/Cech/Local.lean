import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Local.Comparison

noncomputable section

/-! Compatible local comparisons induce a map of the original Cech complexes. -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe u v w uA vA

variable {C : Type u} [Category.{v} C] {A : Type uA} [Category.{vA} A]
  [HasProducts.{w} A] [Preadditive A]
  (E : SimplicialObject (FormalCoproduct.{w} C)) (F G : Cᵒᵖ ⥤ A)
  (a : ∀ (n : SimplexCategory) (i : (E.obj (op n)).I),
    F.obj (op ((E.obj (op n)).obj i)) ⟶ G.obj (op ((E.obj (op n)).obj i)))
  (ha : ∀ {m n : SimplexCategory} (f : m ⟶ n) (i : (E.obj (op n)).I),
    F.map ((E.map f.op).φ i).op ≫ a n i =
      a m ((E.map f.op).f i) ≫ G.map ((E.map f.op).φ i).op)

def cosimplicialMap : (FormalCoproduct.cosimplicialObjectFunctor E).obj F ⟶
    (FormalCoproduct.cosimplicialObjectFunctor E).obj G where
  app n := Limits.Pi.map (a n)
  naturality m n f := by
    apply Limits.Pi.hom_ext
    intro i
    change ((Limits.Pi.lift (fun j : (E.obj (op n)).I =>
      Limits.Pi.π (fun l => F.obj (op ((E.obj (op m)).obj l))) ((E.map f.op).f j) ≫
        F.map ((E.map f.op).φ j).op)) ≫ Limits.Pi.map (a n)) ≫
          Limits.Pi.π (fun j => G.obj (op ((E.obj (op n)).obj j))) i =
      (Limits.Pi.map (a m) ≫ Limits.Pi.lift (fun j : (E.obj (op n)).I =>
        Limits.Pi.π (fun l => G.obj (op ((E.obj (op m)).obj l))) ((E.map f.op).f j) ≫
          G.map ((E.map f.op).φ j).op)) ≫
            Limits.Pi.π (fun j => G.obj (op ((E.obj (op n)).obj j))) i
    simpa only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π,
      Limits.Pi.lift_comp_π_assoc, Limits.Pi.map_π_assoc] using
        congrArg (fun t => Limits.Pi.π (fun j => F.obj (op ((E.obj (op m)).obj j))) ((E.map f.op).f i) ≫ t)
          (ha f i)

def map : (FormalCoproduct.cochainComplexFunctor E).obj F ⟶
    (FormalCoproduct.cochainComplexFunctor E).obj G :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).map (cosimplicialMap E F G a ha)

theorem map_component (n : ℕ) : (Comparison.map E F G a ha).f n = Limits.Pi.map (a ⦋n⦌) := rfl

variable [∀ n i, IsIso (a n i)]

instance cosimplicialMap_isIso : IsIso (cosimplicialMap E F G a ha) := by
  have (n : SimplexCategory) : IsIso ((cosimplicialMap E F G a ha).app n) := by
    change IsIso (Limits.Pi.map (a n))
    infer_instance
  exact NatIso.isIso_of_isIso_app (cosimplicialMap E F G a ha)

instance map_isIso : IsIso (Comparison.map E F G a ha) := by
  let : IsIso (cosimplicialMap E F G a ha) := cosimplicialMap_isIso E F G a ha
  exact CategoryTheory.Functor.map_isIso (AlgebraicTopology.alternatingCofaceMapComplex A)
    (cosimplicialMap E F G a ha)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Local.Comparison
