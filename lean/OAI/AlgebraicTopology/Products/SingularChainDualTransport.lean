import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.Homotopy

/-! # Singular Chain Dual Transport -/

namespace OAI.AlgebraicTopology.Products.SingularChainDualTransport

noncomputable section

section

/-!
# Transport of actual scalar chain maps and homotopies to cochains

The linear Yoneda functor gives the coefficient-module-valued dual of a
chain complex. Genuine singular cochains are identified with this dual by
their already proved evaluation equivalence, including its differential.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- The actual module-valued dual complex functor. -/
abbrev scalarChainDualFunctor (M : ModuleCat.{0} R) :
    (ChainComplex (ModuleCat.{0} R) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) ⋙
    ((linearYoneda R (ModuleCat.{0} R)).obj M).mapHomologicalComplex (ComplexShape.up ℕ)

abbrev scalarChainDual (M : ModuleCat.{0} R) (C : ChainComplex (ModuleCat.{0} R) ℕ) :=
  (scalarChainDualFunctor M).obj (op C)

abbrev scalarChainDualMap (M : ModuleCat.{0} R)
    {C D : ChainComplex (ModuleCat.{0} R) ℕ} (f : C ⟶ D) :=
  (scalarChainDualFunctor M).map f.op

/-- Evaluation identifies genuine singular cochains with the linear dual
of the actual scalar singular-chain complex. -/
def singularLinearCochainDualIso (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Cohomology.Singular.Basic.singularCochains M X ≅ scalarChainDual M (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).trans
      ModuleCat.homLinearEquiv.symm).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      ext c : 1
      apply ModuleCat.hom_ext
      change (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) M i c).comp
          ((Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d j i).hom =
        Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) M j
          ((Cohomology.Singular.Basic.singularCochains M X).d i j c)
      exact (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d (TopCat.toSSet.obj X) M i j c).symm)

/-- Precomposition with an actual chain map, transported to genuine
singular cochains. -/
def singularDualCochainMap (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y) :
    Cohomology.Singular.Basic.singularCochains M Y ⟶ Cohomology.Singular.Basic.singularCochains M X :=
  (singularLinearCochainDualIso M Y).hom ≫ scalarChainDualMap M f ≫
    (singularLinearCochainDualIso M X).inv

/-- On functionals the transported map is exactly precomposition. -/
theorem singularDualCochainMap_dual (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y)
    (n : ℕ) (c : (Cohomology.Singular.Basic.singularCochains M Y).X n) :
    Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n ((singularDualCochainMap M f).f n c) =
      (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M Y n c).comp (f.f n).hom := by
  change Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n
    ((Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

@[simp]
theorem singularDualCochainMap_id (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    singularDualCochainMap M (𝟙 (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X)) = 𝟙 _ := by
  simp [singularDualCochainMap, scalarChainDualMap]

@[reassoc]
theorem singularDualCochainMap_comp (M : ModuleCat.{0} R) {X Y Z : TopCat.{0}}
    (f : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y)
    (g : Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Z) :
    singularDualCochainMap M (f ≫ g) =
      singularDualCochainMap M g ≫ singularDualCochainMap M f := by
  simp [singularDualCochainMap, scalarChainDualMap]

@[simp]
theorem singularDualCochainMap_continuous (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularDualCochainMap M (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) =
      Cohomology.Singular.Functor.singularPullback M f := by
  ext n : 1
  apply ModuleCat.hom_ext
  ext c : 1
  apply (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X n).injective
  rw [singularDualCochainMap_dual]
  exact (Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map f) n c).symm

/-- The linear dual of an actual chain homotopy. -/
def singularDualCochainHomotopy (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    {f g : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y}
    (h : Homotopy f g) : Homotopy (singularDualCochainMap M f) (singularDualCochainMap M g) :=
  (((linearYoneda R (ModuleCat.{0} R)).obj M).mapHomotopy h.op).compLeft
    (singularLinearCochainDualIso M Y).hom |>.compRight
      (singularLinearCochainDualIso M X).inv

/-- Each cochain-homotopy component is precomposition with the actual
chain-homotopy component, with the indices reversed. -/
theorem singularDualCochainHomotopy_dual (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    {f g : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y}
    (h : Homotopy f g) (i j : ℕ) (c : (Cohomology.Singular.Basic.singularCochains M Y).X i) :
    Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j
        ((singularDualCochainHomotopy M h).hom i j c) =
      (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M Y i c).comp (h.hom j i).hom := by
  change Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j
    ((Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

end

/-!
Naturality of the dual of an actual scalar singular-chain homotopy.
The proof uses the existing evaluation equivalence and the actual chain
component equality, with the homotopy indices reversed by duality.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- Componentwise natural scalar chain homotopies induce natural cochain homotopies. -/
@[reassoc]
theorem singularDualCochainHomotopy_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    {aX bX : Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) X}
    {aY bY : Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y}
    (hX : Homotopy aX bX) (hY : Homotopy aY bY)
    (hnat : ∀ i j, (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f i ≫ hY.hom i j =
      hX.hom i j ≫ (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f j) (i j : ℕ) :
    (singularDualCochainHomotopy M hY).hom i j ≫ (Cohomology.Singular.Functor.singularPullback M f).f j =
      (Cohomology.Singular.Functor.singularPullback M f).f i ≫ (singularDualCochainHomotopy M hX).hom i j := by
  apply ModuleCat.hom_ext
  ext c : 1
  apply (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j).injective
  change Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j
      ((Cohomology.Singular.Functor.singularPullback M f).f j ((singularDualCochainHomotopy M hY).hom i j c)) =
    Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X j
      ((singularDualCochainHomotopy M hX).hom i j ((Cohomology.Singular.Functor.singularPullback M f).f i c))
  have hpull (k : ℕ) (u : (Cohomology.Singular.Basic.singularCochains M Y).X k) :
      Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M X k ((Cohomology.Singular.Functor.singularPullback M f).f k u) =
        (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M Y k u).comp
          ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f k).hom :=
    Cohomology.Singular.EvaluationNaturality.degreewiseChainDualEquiv_pullback M (TopCat.toSSet.map f) k u
  rw [hpull, singularDualCochainHomotopy_dual, singularDualCochainHomotopy_dual, hpull]
  ext z
  exact congrArg (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv M Y i c)
    (ConcreteCategory.congr_hom (hnat j i) z)

end

end OAI.AlgebraicTopology.Products.SingularChainDualTransport
