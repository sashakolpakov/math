import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Homotopy Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality

noncomputable section

/-!
# Naturality of the actual singular chain homotopy

A commuting square of topological homotopies gives a commuting square of
the chain homotopy components constructed by mathlib. The proof follows the
actual singular simplicial homotopy and its alternating prism sum. In
particular it applies to restrictions of a homotopy to a subspace pair.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicTopology
open MonoidalCategory Functor.LaxMonoidal
open scoped Simplicial

universe v u w

section SimplicialObjects

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y X' Y' : SimplicialObject C}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The alternating prism construction respects a commuting square of
combinatorial simplicial homotopy components. -/
theorem combinatorialHomotopy_chain_naturality
    (H : SimplicialObject.Homotopy f g) (H' : SimplicialObject.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : ∀ (n : ℕ) (i : Fin (n + 1)),
      u.app (op ⦋n⦌) ≫ H.h i = H'.h i ≫ v.app (op ⦋n + 1⦌))
    (a b : ℕ) :
    ((alternatingFaceMapComplex C).map u).f a ≫ H.toChainHomotopy.hom a b =
      H'.toChainHomotopy.hom a b ≫ ((alternatingFaceMapComplex C).map v).f b := by
  change u.app (op ⦋a⦌) ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom H a b =
    SimplicialObject.Homotopy.ToChainHomotopy.hom H' a b ≫ v.app (op ⦋b⦌)
  by_cases hab : a + 1 = b
  · subst b
    simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, h]
  · simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hab,
      comp_zero, zero_comp]

end SimplicialObjects

section SimplicialSets

variable {X Y X' Y' : SSet.{w}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- A commuting square of geometric simplicial homotopies commutes with
each actual combinatorial prism simplex. -/
theorem simplicialHomotopy_component_naturality
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v)
    (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H.toSimplicialObjectHomotopy.h i =
      H'.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  change ((SSet.yonedaEquiv.symm (u.app (op ⦋n⦌) x) ▷ Δ[1]) ≫ H.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1 =
    v.app _ (((SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ H'.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1)
  rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, h]
  rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Naturality of the actual chain homotopy associated to a homotopy of
simplicial sets, with arbitrary coefficients in a preadditive category. -/
theorem simplicialHomotopy_chain_naturality
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v) (A : C) (a b : ℕ) :
    (SSet.chainComplexMap u A).f a ≫ (H.chainComplexMap A).hom a b =
      (H'.chainComplexMap A).hom a b ≫ (SSet.chainComplexMap v A).f b := by
  apply combinatorialHomotopy_chain_naturality
    (H.toSimplicialObjectHomotopy.whiskerRight ((sigmaConst (C := C)).obj A))
    (H'.toSimplicialObjectHomotopy.whiskerRight ((sigmaConst (C := C)).obj A))
  intro n i
  change ((sigmaConst (C := C)).obj A).map (u.app (op ⦋n⦌)) ≫
      ((sigmaConst (C := C)).obj A).map (H.toSimplicialObjectHomotopy.h i) =
    ((sigmaConst (C := C)).obj A).map (H'.toSimplicialObjectHomotopy.h i) ≫
      ((sigmaConst (C := C)).obj A).map (v.app (op ⦋n + 1⦌))
  simpa only [Functor.map_comp] using congrArg (((sigmaConst (C := C)).obj A).map)
    (simplicialHomotopy_component_naturality H H' u v h n i)

end SimplicialSets

variable {X Y X' Y' : TopCat.{w}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The actual singular simplicial homotopies preserve a commuting
topological homotopy square. -/
theorem topologicalHomotopy_simplicial_square
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) :
    (TopCat.toSSet.map u ▷ Δ[1]) ≫ H.toSSet.h =
      H'.toSSet.h ≫ TopCat.toSSet.map v := by
  change (TopCat.toSSet.map u ▷ Δ[1]) ≫
      (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
        μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map H.h) =
    (TopCat.toSSet.obj X' ◁ SSet.stdSimplex.toSSetObjI ≫
        μ TopCat.toSSet X' TopCat.I ≫ TopCat.toSSet.map H'.h) ≫ TopCat.toSSet.map v
  rw [← whisker_exchange_assoc]
  rw [μ_natural_left_assoc]
  rw [← TopCat.toSSet.map_comp, h, TopCat.toSSet.map_comp]
  simp only [Category.assoc]

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Every degree of the actual singular chain homotopy is natural under
a commuting square of topological homotopies. -/
theorem topologicalHomotopy_chain_naturality
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) (A : C) (a b : ℕ) :
    (((singularChainComplexFunctor C).obj A).map u).f a ≫
        (H.singularChainComplexFunctorObjMap A).hom a b =
      (H'.singularChainComplexFunctorObjMap A).hom a b ≫
        (((singularChainComplexFunctor C).obj A).map v).f b :=
  simplicialHomotopy_chain_naturality H.toSSet H'.toSSet
    (TopCat.toSSet.map u) (TopCat.toSSet.map v)
    (topologicalHomotopy_simplicial_square H H' u v h) A a b

end

end OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality
