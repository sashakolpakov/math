import OAI.AlgebraicTopology.Cohomology.Singular.Basic

/-! # Coefficients -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

noncomputable section

section

/-!
# Degreewise meaning of the singular cochain complex

The opposite-category construction in `Basic` has all functions on genuine
simplices as its degreewise objects. In particular, there is no finite-support
restriction on cochains. The final isomorphism indexes these functions directly
by continuous maps from mathlib's standard topological simplex.

The product/coproduct argument generalizes the checked
`OppositeCochainAudit.lean` from the frozen September 2026 audit, replacing its
rational coefficient module with an arbitrary module over a ring.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R : Type} [Ring R]

/-- Evaluate a simplicial cochain at a simplex. -/
def simplicialEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    (s : K _⦋n⦌) : (Basic.simplicialCochains K M).X n ⟶ M :=
  (K.ιChainComplex (R := op M) s).unop

/-- Cochains in degree `n` are all module-valued functions on the `n`-simplices. -/
def degreewiseFunctionIso (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Basic.simplicialCochains K M).X n ≅ ModuleCat.of R (K _⦋n⦌ → M) :=
  (opProductIsoCoproduct (fun _ : K _⦋n⦌ => M)).unop ≪≫
    ModuleCat.piIsoPi (fun _ : K _⦋n⦌ => M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degreewise isomorphism respects evaluation at each simplex. -/
theorem degreewiseFunctionIso_evaluation (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n⦌) :
    (degreewiseFunctionIso K M n).hom ≫ ModuleCat.ofHom (LinearMap.proj s) =
      simplicialEvaluation K M s := by
  simp only [degreewiseFunctionIso, Iso.trans_hom, Iso.unop_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype]
  simpa only [simplicialEvaluation, SSet.ιChainComplex, unop_comp,
    Quiver.Hom.unop_op] using
    congrArg Quiver.Hom.unop (π_comp_opProductIsoCoproduct_hom
      (fun _ : K _⦋n⦌ => M) s)

/-- Function coordinates of a cochain, evaluated at a simplex. -/
@[simp]
theorem degreewiseFunctionIso_hom_apply (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n⦌) :
    (degreewiseFunctionIso K M n).hom c s = simplicialEvaluation K M s c := by
  exact ConcreteCategory.congr_hom (degreewiseFunctionIso_evaluation K M s) c

/-- The singular cochain object is the module of all functions on singular simplices. -/
def singularDegreewiseFunctionIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (Basic.singularCochains M X).X n ≅ ModuleCat.of R (Basic.singularSimplices X n → M) :=
  degreewiseFunctionIso (TopCat.toSSet.obj X) M n

/-- A genuine singular simplex is a continuous map from the standard simplex. -/
def singularSimplicesEquivContinuousMap (X : TopCat.{0}) (n : ℕ) :
    Basic.singularSimplices X n ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv X (op ⦋n⦌)

/-- The degree-`n` singular cochain object is the module of all functions on the
continuous maps from the standard topological `n`-simplex. -/
def singularDegreewiseContinuousFunctionIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    (Basic.singularCochains M X).X n ≅
      ModuleCat.of R (C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M) :=
  singularDegreewiseFunctionIso M X n ≪≫
    (LinearEquiv.piCongrLeft' R (fun _ : Basic.singularSimplices X n => M)
      (singularSimplicesEquivContinuousMap X n)).toModuleIso

end

/-!
# Coefficient maps in genuine singular cohomology

The maps below are induced by mathlib's singular chain functor in the
opposite category of modules. Applying the unop functor turns the map induced
by `f.op` into the ordinary covariant coefficient map on singular cochains.
No cohomology groups or comparison maps are supplied as extra data.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]
variable {M N P : ModuleCat.{0} R}

/-- The cochain map induced by a linear map of coefficient modules. -/
def coefficientCochainMap (f : M ⟶ N) (X : TopCat.{0}) :
    Basic.singularCochains M X ⟶ Basic.singularCochains N X :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)ᵒᵖ).map
      f.op).app X).op

@[simp]
theorem coefficientCochainMap_id (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    coefficientCochainMap (𝟙 M) X = 𝟙 (Basic.singularCochains M X) := by
  simp [coefficientCochainMap]
  exact (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_id _

@[simp]
theorem coefficientCochainMap_comp (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0}) :
    coefficientCochainMap (f ≫ g) X =
      coefficientCochainMap f X ≫ coefficientCochainMap g X := by
  simp [coefficientCochainMap]
  exact (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_comp _ _

/-- On each simplex, a coefficient map postcomposes evaluation with `f`. -/
@[reassoc]
theorem coefficientCochainMap_evaluation (f : M ⟶ N) (X : TopCat.{0})
    {n : ℕ} (s : Basic.singularSimplices X n) :
    (coefficientCochainMap f X).f n ≫ simplicialEvaluation (TopCat.toSSet.obj X) N s =
      simplicialEvaluation (TopCat.toSSet.obj X) M s ≫ f := by
  change (CategoryTheory.Limits.Sigma.map
      (fun _ : Basic.singularSimplices X n => f.op)).unop ≫
      (CategoryTheory.Limits.Sigma.ι (fun _ : Basic.singularSimplices X n => op N) s).unop =
    (CategoryTheory.Limits.Sigma.ι (fun _ : Basic.singularSimplices X n => op M) s).unop ≫ f
  rw [← unop_comp, CategoryTheory.Limits.Sigma.ι_map]
  rfl

/-- In the established function coordinates, a coefficient map acts pointwise. -/
@[simp]
theorem coefficientCochainMap_apply (f : M ⟶ N) (X : TopCat.{0})
    {n : ℕ} (c : (Basic.singularCochains M X).X n) (s : Basic.singularSimplices X n) :
    (singularDegreewiseFunctionIso N X n).hom ((coefficientCochainMap f X).f n c) s =
      f ((singularDegreewiseFunctionIso M X n).hom c s) := by
  calc
    _ = simplicialEvaluation (TopCat.toSSet.obj X) N s
        ((coefficientCochainMap f X).f n c) :=
      degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) N _ s
    _ = f (simplicialEvaluation (TopCat.toSSet.obj X) M s c) :=
      ConcreteCategory.congr_hom (coefficientCochainMap_evaluation f X s) c
    _ = _ := congrArg (fun x : M => f x)
      (degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) M c s).symm

/-- The singular cohomology map induced by a linear coefficient map. -/
def coefficientMap (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n ⟶ Basic.singularCohomology N X n :=
  HomologicalComplex.homologyMap (coefficientCochainMap f X) n

@[simp]
theorem coefficientMap_id (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    coefficientMap (𝟙 M) X n = 𝟙 (Basic.singularCohomology M X n) := by
  simp [coefficientMap]

@[simp]
theorem coefficientMap_comp (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0}) (n : ℕ) :
    coefficientMap (f ≫ g) X n = coefficientMap f X n ≫ coefficientMap g X n := by
  simp [coefficientMap, HomologicalComplex.homologyMap_comp]

/-- For a fixed space, singular cochains are functorial in the coefficient module. -/
def coefficientCochainFunctor (X : TopCat.{0}) :
    ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} R) ℕ where
  obj M := Basic.singularCochains M X
  map f := coefficientCochainMap f X

/-- For a fixed space and degree, singular cohomology is functorial in coefficients. -/
def coefficientFunctor (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R ⥤ ModuleCat.{0} R where
  obj M := Basic.singularCohomology M X n
  map f := coefficientMap f X n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
