import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel

/-! # Homology Zero Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality.Cycles

noncomputable section

/-!
# Naturality of the actual zeroth singular-homology augmentation

The augmentation sends every genuine vertex class to the coefficient module's
identity. Since those classes jointly generate H0, this proves naturality under
actual simplicial and continuous maps, and under the homology isomorphisms of
actual homotopy equivalences.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

variable {R : Type} [Ring R]

/-- The actual H0 class of a vertex, with coefficients in a module. -/
def simplicialH0Generator (S : SSet.{0}) (M : ModuleCat.{0} R) (x : S _⦋0⦌) :
    M ⟶ S.homology M 0 :=
  (S.chainComplex M).liftCycles (S.ιChainComplex x) 0 (by simp) (by simp) ≫
    (S.chainComplex M).homologyπ 0

set_option backward.isDefEq.respectTransparency false in
/-- Every vertex class has augmentation one. -/
@[reassoc (attr := simp)]
theorem simplicialH0Generator_augmentation (S : SSet.{0}) (M : ModuleCat.{0} R)
    (x : S _⦋0⦌) :
    simplicialH0Generator S M x ≫ S.homology₀ε M = 𝟙 M := by
  simpa only [simplicialH0Generator, Category.assoc] using
    S.liftCycles_ιChainComplex_homologyπ_homology₀ε M x

set_option backward.isDefEq.respectTransparency false in
/-- Vertex classes determine every homomorphism out of H0. -/
theorem simplicialH0_hom_ext (S : SSet.{0}) (M : ModuleCat.{0} R)
    {N : ModuleCat.{0} R} {f g : S.homology M 0 ⟶ N}
    (h : ∀ x, simplicialH0Generator S M x ≫ f = simplicialH0Generator S M x ≫ g) :
    f = g := by
  apply (cancel_epi ((S.chainComplex M).homologyπ 0)).mp
  apply (cancel_epi (S.chainComplex M).cycles₀Iso.inv).mp
  apply SSet.chainComplex_hom_ext
  intro x
  have hx : S.ιChainComplex x ≫ (S.chainComplex M).cycles₀Iso.inv =
      (S.chainComplex M).liftCycles (S.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((S.chainComplex M).iCycles 0)).mp
    simp
  simpa only [simplicialH0Generator, ← Category.assoc, hx] using h x

set_option backward.isDefEq.respectTransparency false in
/-- The class of a vertex is carried to the class of its image vertex. -/
@[reassoc]
theorem simplicialH0Generator_naturality {S T : SSet.{0}} (f : S ⟶ T)
    (M : ModuleCat.{0} R) (x : S _⦋0⦌) :
    simplicialH0Generator S M x ≫ SSet.homologyMap f M 0 =
      simplicialH0Generator T M (f.app _ x) := by
  simp [simplicialH0Generator, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual simplicial H0 augmentation. -/
@[reassoc]
theorem simplicialH0_augmentation_naturality {S T : SSet.{0}} (f : S ⟶ T)
    (M : ModuleCat.{0} R) :
    SSet.homologyMap f M 0 ≫ T.homology₀ε M = S.homology₀ε M := by
  apply simplicialH0_hom_ext S M
  intro x
  simp only [← Category.assoc, simplicialH0Generator_naturality,
    simplicialH0Generator_augmentation]

/-- Naturality under a genuine continuous map of spaces. -/
@[reassoc]
theorem singularH0_augmentation_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (M : ModuleCat.{0} R) :
    HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map f) 0 ≫
      Y.singularHomology₀ε M = X.singularHomology₀ε M :=
  simplicialH0_augmentation_naturality (TopCat.toSSet.map f) M

/-- Integral naturality in the homology notation used by the relative-chain construction. -/
@[reassoc]
theorem integralSingularH0_augmentation_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 ≫ Y.singularHomology₀ε (ModuleCat.of ℤ ℤ) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) :=
  singularH0_augmentation_naturality f (ModuleCat.of ℤ ℤ)

/-- The homology isomorphism induced by an actual homotopy equivalence preserves augmentation. -/
@[reassoc]
theorem singularH0_augmentation_homotopyEquiv {X Y : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv X Y) (M : ModuleCat.{0} R) :
    (ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv M e 0).hom ≫ Y.singularHomology₀ε M =
      X.singularHomology₀ε M :=
  singularH0_augmentation_naturality (TopCat.ofHom e.toFun) M

/-- The inverse homology isomorphism preserves augmentation as well. -/
@[reassoc]
theorem singularH0_augmentation_homotopyEquiv_inv {X Y : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv X Y) (M : ModuleCat.{0} R) :
    (ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv M e 0).inv ≫ X.singularHomology₀ε M =
      Y.singularHomology₀ε M :=
  singularH0_augmentation_naturality (TopCat.ofHom e.invFun) M

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality.Cycles
