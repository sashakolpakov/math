import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleGlobalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SingleFunctorCoordinates

/-! # Mapped Single Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleGlobal

noncomputable section

/-! The genuine principal comparison commutes with a map from the
original mapped single complex to an arbitrary target complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  {A : Type w} [Category.{z} A] [Abelian A]
  (J : A ⥤ (Opens X)ᵒᵖ ⥤ D) [J.Additive] (M : A)

abbrev sourceComplex (c : ℕ) :=
  (J.mapHomologicalComplex (.up ℕ)).obj ((single A (.up ℕ) c).obj M)

section Maps
variable (c g : ℕ) (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
  (a : sourceComplex J M c ⟶ K)
  {μ : Type u} [LinearOrder μ] (V : μ → Opens X)

abbrev globalIso :=
  Functor.SingleTotal.homologyIso (J ⋙ OrderedCech.Functor.Projection.functor V) M c g

variable [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c))]

def globalMap : (OrderedCech.Projection.complex V (J.obj M)).homology g ⟶
    (Presheaf.OrderedCechEdge.sections K).homology (g+c) :=
  (globalIso J M c g V).inv ≫
    homologyMap ((OrderedCech.TotalProjection.ordered V).map a) (g+c) ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c))

theorem global_coordinates :
    (globalIso J M c g V).hom ≫ globalMap J M c g K a V =
      homologyMap ((OrderedCech.TotalProjection.ordered V).map a) (g+c) ≫
        inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c)) := by
  simp only [globalMap, Iso.hom_inv_id_assoc]

end Maps

theorem globalMap_diagonal (g : ℕ) (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
    (a : sourceComplex J M g ⟶ K) {μ : Type u} [LinearOrder μ] (V : μ → Opens X)
    [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+g))] :
    globalMap J M g g K a V = Mapped.SingleGlobalSource.map J M g K a V := rfl

variable (c g : ℕ) (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
  (a : sourceComplex J M c ⟶ K)
  {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F]
  (B : κ → Opens X) (E : ν → Opens X)
  (r : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B E s (sourceComplex J M c) (g+c))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B E s K (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (sourceComplex J M c)) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) (g+c))]
  [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c))]

abbrev localIso := Functor.SingleTotal.homologyIso
  (J ⋙ Cech.SingleFunctorCoordinates.localFunctor F W) M c g

theorem comparison :
    PresheafCover.Comparison.comparison F W B E r s V T l t (sourceComplex J M c) (g+c) ≫
      (globalIso J M c g V).hom ≫ globalMap J M c g K a V =
    homologyMap (PresheafCover.Comparison.totalMap F W a) (g+c) ≫
      PresheafCover.Comparison.comparison F W B E r s V T l t K (g+c) ≫
        inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c)) := by
  rw [global_coordinates]
  simpa only [Presheaf.OrderedCover.Comparison.totalFunctor,
    OrderedCech.TotalProjection.ordered, Category.assoc] using
    (congrArg (fun f => f ≫ inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c)))
      (PresheafCover.Comparison.naturality F W B E r s V T l t a (g+c))).symm

theorem local_coordinates :
    (localIso J M c g F W).inv ≫
      PresheafCover.Comparison.comparison F W B E r s V T l t (sourceComplex J M c) (g+c) ≫
      (globalIso J M c g V).hom ≫ globalMap J M c g K a V =
    (localIso J M c g F W).inv ≫
      homologyMap (PresheafCover.Comparison.totalMap F W a) (g+c) ≫
      PresheafCover.Comparison.comparison F W B E r s V T l t K (g+c) ≫
        inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) (g+c)) :=
  congrArg (fun f => (localIso J M c g F W).inv ≫ f)
    (comparison J M c g K a F W B E r s V T l t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleGlobal
