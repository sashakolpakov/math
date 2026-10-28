import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.Additive

/-! # Cech Functor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorComparison

noncomputable section

/-! An additive functor preserving finite products commutes with the Cech complex of a finite cover. The comparison is the actual product comparison on every tuple, with no exactness hypothesis on the functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology Opposite
universe u v w uA vA uB vB

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
variable [HasProducts.{w} A] [HasProducts.{w} B]

theorem functorProductComparison_naturality (T : A ⥤ B)
    {I J : Type w} (P : I → A) (Q : J → A) (a : J → I) (φ : ∀ j, P (a j) ⟶ Q j) :
    T.map (Pi.lift fun j => Pi.π P (a j) ≫ φ j) ≫ piComparison T Q =
      piComparison T P ≫ Pi.lift (fun j => Pi.π (fun i => T.obj (P i)) (a j) ≫ T.map (φ j)) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π, ← Functor.map_comp]
  rw [piComparison_comp_π_assoc, ← Functor.map_comp]

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable [Preadditive A] [Preadditive B]
variable (T : A ⥤ B) [T.Additive] [PreservesFiniteProducts T]
variable (P : Cᵒᵖ ⥤ A) {ι : Type w} [Finite ι] (U : ι → C)

def finiteCechCosimplicialFunctorIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P ⋙ T ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj (P ⋙ T) :=
  NatIso.ofComponents (fun q => by
    let V := ((FormalCoproduct.mk _ U).cech.rightOp.obj q).unop
    have : Finite V.I := by
      change Finite (ToType q → ι)
      infer_instance
    exact PreservesProduct.iso T (fun i : V.I => P.obj (op (V.obj i)))) (by
      intro q r f
      let V := ((FormalCoproduct.mk _ U).cech.rightOp.obj q).unop
      let W := ((FormalCoproduct.mk _ U).cech.rightOp.obj r).unop
      let a := (FormalCoproduct.mk _ U).cech.map f.op
      exact functorProductComparison_naturality T
        (fun i : V.I => P.obj (op (V.obj i))) (fun i : W.I => P.obj (op (W.obj i)))
        a.f (fun i => P.map (a.φ i).op))

theorem finiteCechCosimplicialFunctorIso_comm_d (n : ℕ) :
    (finiteCechCosimplicialFunctorIso T P U).hom.app (SimplexCategory.mk n) ≫
        AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj (P ⋙ T)) n =
      T.map (AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) n) ≫
        (finiteCechCosimplicialFunctorIso T P U).hom.app (SimplexCategory.mk (n + 1)) := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
    Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    ((finiteCechCosimplicialFunctorIso T P U).hom.naturality (SimplexCategory.δ k)).symm

omit [Finite ι] in
private theorem genericCech_d_succ (n : ℕ) :
    ((cechComplexFunctor U).obj P).d n (n + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) n := by
  change ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech).obj P).d
    n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

def finiteCechFunctorIso :
    (T.mapHomologicalComplex (.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ T) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (finiteCechCosimplicialFunctorIso T P U).app (SimplexCategory.mk n)) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Functor.mapHomologicalComplex_obj_d, genericCech_d_succ, genericCech_d_succ]
      exact finiteCechCosimplicialFunctorIso_comm_d T P U i)

@[reassoc]
theorem finiteCechFunctorIso_hom_f_π (n : ℕ) (i : Fin (n + 1) → ι) :
    (finiteCechFunctorIso T P U).hom.f n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          T.obj (P.obj (op (∏ᶜ fun k => U (j k))))) i =
      T.map (Pi.π (fun j : Fin (n + 1) → ι => P.obj (op (∏ᶜ fun k => U (j k)))) i) :=
  piComparison_comp_π T _ i

omit [Finite ι] in
theorem cechComplex_map_isIso_of_intersections
    {P Q : Cᵒᵖ ⥤ B} (a : P ⟶ Q)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsIso (a.app (op (∏ᶜ fun k => U (i k))))) :
    IsIso ((cechComplexFunctor U).map a) := by
  have (n : ℕ) : IsIso (((cechComplexFunctor U).map a).f n) := by
    have : ∀ i : Fin (n + 1) → ι, IsIso (a.app (op (∏ᶜ fun k => U (i k)))) := h n
    change IsIso (CategoryTheory.Limits.Pi.map (fun i : Fin (n + 1) → ι => a.app (op (∏ᶜ fun k => U (i k)))))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorComparison
