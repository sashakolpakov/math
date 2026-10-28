import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleCoordinates

/-! # Mapped Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates

noncomputable section

/-! The actual principal comparison of a mapped single complex has
the original single-total coordinates and the same literal coefficient
comparison, independently of its single degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem isIso_of_square {C : Type*} [Category C]
    {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') (e : A ≅ A') (f : B ≅ B')
    [IsIso a] (h : a ≫ f.hom = e.hom ≫ b) : IsIso b := by
  have hb : b = e.inv ≫ a ≫ f.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

private theorem paste {C : Type*} [Category C] {A B D E L R : C}
    (a : A ⟶ B) (b : D ⟶ E) (lo : A ⟶ D) (go : B ⟶ E)
    (lp : D ⟶ L) (gp : E ⟶ R) (lc : A ⟶ L) (gc : B ⟶ R) (v : L ⟶ R)
    (hn : lo ≫ b = a ≫ go) (hp : b ≫ gp = lp ≫ v)
    (hl : lo ≫ lp = lc) (hg : go ≫ gp = gc) : a ≫ gc = lc ≫ v := by
  rw [← hg, ← Category.assoc, ← hn, Category.assoc, hp, ← Category.assoc, hl]

universe u v w z
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  {A : Type w} [Category.{z} A] [Abelian A]
  (J : A ⥤ (Opens X)ᵒᵖ ⥤ D) [J.Additive] (M : A) (c g : ℕ)

abbrev source := MappedSingleGlobal.sourceComplex J M c
abbrev plain := (single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj (J.obj M)
abbrev singleIso := (singleMapHomologicalComplex J (.up ℕ) c).app M

section Relative
variable (U : Opens X) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → Opens X) (T : κ → Opens X)
  (r : FormalCoproduct.mk κ T ⟶ FormalCoproduct.mk ι V)

abbrev relativeIso := homologyMapIso
  (HomologicalComplex₂.total.mapIso
    (((RelativeCech.Total.localFunctor U V).mapHomologicalComplex (.up ℕ)).mapIso
      (singleIso J M c)) (.up ℕ)) (g+c)

variable [IsIso (RelativeCech.Refinement.homology U V T r (source J M c) (g+c))]

theorem relative_isIso :
    IsIso (RelativeCech.Refinement.homology U V T r (plain J M c) (g+c)) :=
  isIso_of_square (RelativeCech.Refinement.homology U V T r (source J M c) (g+c))
    (RelativeCech.Refinement.homology U V T r (plain J M c) (g+c))
    (relativeIso J M c g U V) (relativeIso J M c g U T)
    (RelativeCech.Refinement.homology_naturality U V T r
      (K := source J M c) (L := plain J M c) (singleIso J M c).hom (g+c)).symm
end Relative

section Ordered
variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → Opens X) (T : κ → Opens X)
  (r : FormalCoproduct.mk κ T ⟶ FormalCoproduct.mk ι V)

abbrev orderedIso := homologyMapIso
  ((OrderedCech.TotalProjection.ordered V).mapIso (singleIso J M c)) (g+c)

variable [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T r (source J M c)) (g+c))]

theorem ordered_isIso :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V T r (plain J M c)) (g+c)) :=
  isIso_of_square (homologyMap (OrderedCech.Refinement.totalMap V T r (source J M c)) (g+c))
    (homologyMap (OrderedCech.Refinement.totalMap V T r (plain J M c)) (g+c))
    (orderedIso J M c g V) (orderedIso J M c g T)
    (Presheaf.OrderedCover.Comparison.homology_naturality V T r
      (K := source J M c) (L := plain J M c) (singleIso J M c).hom (g+c)).symm
end Ordered

variable {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (E : ν → Opens X)
  (r : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B E s (source J M c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source J M c)) (g+c))]

abbrev localCoordinates := Functor.SingleTotal.homologyIso
  (J ⋙ Cech.SingleFunctorCoordinates.localFunctor F W) M c g
abbrev globalCoordinates := Functor.SingleTotal.homologyIso
  (J ⋙ OrderedCech.Functor.Projection.functor V) M c g

def coefficientComparison := by
  letI := relative_isIso J M c g (F.obj (⊤_ C)) B E s
  letI := ordered_isIso J M c g V T t
  exact PresheafSingleCoordinates.coefficientComparison
    (J.obj M) c g F W B E r s V T l t

theorem comparison :
    PresheafCover.Comparison.comparison F W B E r s V T l t (source J M c) (g+c) ≫
      (globalCoordinates J M c g V).hom =
    (localCoordinates J M c g F W).hom ≫ coefficientComparison J M c g F W B E r s V T l t := by
  let := relative_isIso J M c g (F.obj (⊤_ C)) B E s
  let := ordered_isIso J M c g V T t
  have hn := PresheafCover.Comparison.naturality
    F W B E r s V T l t (K := source J M c) (L := plain J M c) (singleIso J M c).hom (g+c)
  have hp := PresheafSingleCoordinates.comparison (J.obj M) c g F W B E r s V T l t
  have hl := Functor.MappedSingleCoordinates.comparison J
    (Cech.SingleFunctorCoordinates.localFunctor F W) M c g
  have hg := Functor.MappedSingleCoordinates.comparison J
    (OrderedCech.Functor.Projection.functor V) M c g
  exact paste _ _ _ _ _ _ _ _ _ hn hp hl hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates
