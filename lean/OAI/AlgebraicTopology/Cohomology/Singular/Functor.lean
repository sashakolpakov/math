import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

/-! # Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Functor

noncomputable section

/-!
# Pullback on genuine singular cochains

The covariant simplicial chain functor, evaluated in the opposite category of
modules, becomes a contravariant cochain functor after passing back from that
opposite category. The maps below therefore pull back actual cochains and their
cohomology along continuous maps.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]

/-- Simplicial cochains depend contravariantly on the simplicial set. -/
def simplicialCochainsFunctor (M : ModuleCat.{0} R) :
    SSet.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  ((SSet.chainComplexFunctor ((ModuleCat.{0} R)ᵒᵖ)).obj (op M)).op ⋙
    HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)

/-- Pullback of cochains along a morphism of simplicial sets. -/
def simplicialPullback (M : ModuleCat.{0} R) {K L : SSet.{0}} (f : K ⟶ L) :
    Basic.simplicialCochains L M ⟶ Basic.simplicialCochains K M :=
  (simplicialCochainsFunctor M).map f.op

@[simp]
theorem simplicialPullback_id (M : ModuleCat.{0} R) (K : SSet.{0}) :
    simplicialPullback M (𝟙 K) = 𝟙 (Basic.simplicialCochains K M) :=
  (simplicialCochainsFunctor M).map_id (op K)

@[simp]
theorem simplicialPullback_comp (M : ModuleCat.{0} R)
    {K L N : SSet.{0}} (f : K ⟶ L) (g : L ⟶ N) :
    simplicialPullback M (f ≫ g) = simplicialPullback M g ≫ simplicialPullback M f :=
  (simplicialCochainsFunctor M).map_comp g.op f.op

/-- Singular cochains as a contravariant functor on topological spaces. -/
def singularCochainsFunctor (M : ModuleCat.{0} R) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  TopCat.toSSet.op ⋙ simplicialCochainsFunctor M

/-- Pullback of singular cochains along a continuous map. -/
def singularPullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Basic.singularCochains M Y ⟶ Basic.singularCochains M X :=
  (singularCochainsFunctor M).map f.op

@[simp]
theorem singularPullback_id (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    singularPullback M (𝟙 X) = 𝟙 (Basic.singularCochains M X) :=
  (singularCochainsFunctor M).map_id (op X)

@[simp]
theorem singularPullback_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularPullback M (f ≫ g) = singularPullback M g ≫ singularPullback M f :=
  (singularCochainsFunctor M).map_comp g.op f.op

/-- Pullback of singular cohomology classes along a continuous map. -/
def singularCohomologyPullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) : Basic.singularCohomology M Y n ⟶ Basic.singularCohomology M X n :=
  HomologicalComplex.homologyMap (singularPullback M f) n

@[simp]
theorem singularCohomologyPullback_id (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCohomologyPullback M (𝟙 X) n = 𝟙 (Basic.singularCohomology M X n) := by
  simp only [singularCohomologyPullback, singularPullback_id,
    HomologicalComplex.homologyMap_id]

@[simp]
theorem singularCohomologyPullback_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    singularCohomologyPullback M (f ≫ g) n =
      singularCohomologyPullback M g n ≫ singularCohomologyPullback M f n := by
  simp only [singularCohomologyPullback, singularPullback_comp,
    HomologicalComplex.homologyMap_comp]

/-- Singular cohomology in a fixed degree as a contravariant functor. -/
def singularCohomologyFunctor (M : ModuleCat.{0} R) (n : ℕ) :
    TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} R :=
  singularCochainsFunctor M ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- Changing coefficients commutes with pullback along a continuous map. -/
theorem coefficientCochainMap_naturality {M N : ModuleCat.{0} R} (u : M ⟶ N)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularPullback M f ≫ Coefficients.coefficientCochainMap u X =
      Coefficients.coefficientCochainMap u Y ≫ singularPullback N f := by
  let F := AlgebraicTopology.singularChainComplexFunctor ((ModuleCat.{0} R)ᵒᵖ)
  let U := HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)
  change U.map (((F.obj (op M)).map f).op) ≫ U.map (((F.map u.op).app X).op) =
    U.map (((F.map u.op).app Y).op) ≫ U.map (((F.obj (op N)).map f).op)
  rw [← U.map_comp, ← U.map_comp]
  exact congrArg U.map (congrArg Quiver.Hom.op ((F.map u.op).naturality f).symm)

/-- Coefficient maps commute with pullback on singular cohomology. -/
theorem coefficientMap_naturality {M N : ModuleCat.{0} R} (u : M ⟶ N)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyPullback M f n ≫ Coefficients.coefficientMap u X n =
      Coefficients.coefficientMap u Y n ≫ singularCohomologyPullback N f n := by
  simp only [singularCohomologyPullback, Coefficients.coefficientMap,
    ← HomologicalComplex.homologyMap_comp]
  rw [coefficientCochainMap_naturality]

end

end OAI.AlgebraicTopology.Cohomology.Singular.Functor
