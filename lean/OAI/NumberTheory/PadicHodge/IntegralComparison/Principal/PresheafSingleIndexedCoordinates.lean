import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleCoordinates

/-! # Presheaf Single Indexed Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleIndexedCoordinates

noncomputable section

/-! The original principal-to-cover single-coordinate square retains
an explicit total-degree equality. In particular it applies with
q = c + g and the canonical equality c + g = g + c. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  (P : (Opens X)ᵒᵖ ⥤ D) (c g : ℕ)
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (q : ℕ) (hq : q = g+c)

def sourceIso :=
  eqToIso (congrArg (fun j => ((Functor.SingleTotal.bicomplex (Cech.SingleFunctorCoordinates.localFunctor F W)
    P c).total (.up ℕ)).homology j) hq) ≪≫
      Functor.SingleTotal.homologyIso (Cech.SingleFunctorCoordinates.localFunctor F W) P c g

def targetIso :=
  eqToIso (congrArg (fun j => ((Functor.SingleTotal.bicomplex (OrderedCech.Functor.Projection.functor V)
    P c).total (.up ℕ)).homology j) hq) ≪≫
      Functor.SingleTotal.homologyIso (OrderedCech.Functor.Projection.functor V) P c g

variable
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P)) q)]

def coefficientComparison :
    (AugmentedOrdered.Cech.complex W (F.op ⋙ P)).homology g ⟶
      (OrderedCech.Projection.complex V P).homology g := by
  subst q
  exact PresheafSingleCoordinates.coefficientComparison P c g F W B J r s V T l t

theorem comparison :
    PresheafCover.Comparison.comparison F W B J r s V T l t
      ((single ((Opens X)ᵒᵖ ⥤ D) (.up ℕ) c).obj P) q ≫ (targetIso P c g V q hq).hom =
    (sourceIso P c g F W q hq).hom ≫
      coefficientComparison P c g F W B J r s V T l t q hq := by
  subst q
  simpa only [sourceIso, targetIso, coefficientComparison, eqToIso_refl, Iso.refl_trans] using
    PresheafSingleCoordinates.comparison P c g F W B J r s V T l t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleIndexedCoordinates
