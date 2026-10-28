import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Rational Singular Chains -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles

noncomputable section

/-!
# Change of coefficients for genuine singular chains

An additive functor preserving coproducts commutes with the actual simplicial
chain construction. The degreewise isomorphism sends the image of each simplex
summand to the corresponding simplex summand with its coefficient transported
by the specified coefficient isomorphism.
-/

open Simplicial _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe w u₁ u₂ v₁ v₂

section CoefficientFunctor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasCoproducts.{w} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasCoproducts.{w} D]
variable (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
variable (R : C) (S : D) (e : F.obj R ≅ S)

/-- The actual degreewise coproduct comparison for simplicial chains. -/
def coefficientFunctorChainDegreeIso (K : SSet.{w}) (n : ℕ) :
    F.obj ((K.chainComplex R).X n) ≅ (K.chainComplex S).X n :=
  (asIso (sigmaComparison F (fun _ : K _⦋n⦌ => R))).symm ≪≫
    Sigma.mapIso (fun _ => e)

/-- On each simplex summand, the coproduct comparison applies precisely the
chosen coefficient isomorphism. -/
@[reassoc (attr := simp)]
theorem coefficientFunctorChainDegreeIso_ι (K : SSet.{w}) (n : ℕ) (x : K _⦋n⦌) :
    F.map (K.ιChainComplex (R := R) x) ≫
        (coefficientFunctorChainDegreeIso F R S e K n).hom =
      e.hom ≫ K.ιChainComplex (R := S) x := by
  change F.map (Sigma.ι (fun _ : K _⦋n⦌ => R) x) ≫
    inv (sigmaComparison F (fun _ : K _⦋n⦌ => R)) ≫
    (Sigma.mapIso (fun _ : K _⦋n⦌ => e)).hom =
      e.hom ≫ Sigma.ι (fun _ : K _⦋n⦌ => S) x
  rw [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

omit [Preadditive D] [HasCoproducts D] in
/-- The images of the actual simplex summands are jointly epimorphic. -/
theorem coefficientFunctorChain_hom_ext (K : SSet.{w}) (n : ℕ) {T : D}
    {f g : F.obj ((K.chainComplex R).X n) ⟶ T}
    (h : ∀ x : K _⦋n⦌,
      F.map (K.ιChainComplex (R := R) x) ≫ f =
        F.map (K.ιChainComplex (R := R) x) ≫ g) : f = g := by
  apply (isColimitCofanMkObjOfIsColimit F (fun _ : K _⦋n⦌ => R)
    (fun x => K.ιChainComplex (R := R) x) (K.isColimitChainComplexXCofan R n)).hom_ext
  intro x
  exact h x.as

variable [F.Additive]

/-- Coproduct comparison commutes with the alternating face differential. -/
theorem coefficientFunctorChainDegreeIso_comm (K : SSet.{w}) (n : ℕ) :
    (coefficientFunctorChainDegreeIso F R S e K (n + 1)).hom ≫
        (K.chainComplex S).d (n + 1) n =
      F.map ((K.chainComplex R).d (n + 1) n) ≫
        (coefficientFunctorChainDegreeIso F R S e K n).hom := by
  apply coefficientFunctorChain_hom_ext F R K (n + 1)
  intro x
  rw [← Category.assoc, coefficientFunctorChainDegreeIso_ι, Category.assoc,
    SSet.ιChainComplex_d, ← F.map_comp_assoc, SSet.ιChainComplex_d]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    coefficientFunctorChainDegreeIso_ι]

/-- An additive coproduct-preserving coefficient functor commutes with the
actual simplicial chain complex, including its boundary maps. -/
def coefficientFunctorChainsIso (K : SSet.{w}) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.chainComplex R) ≅
      K.chainComplex S :=
  HomologicalComplex.Hom.isoOfComponents
    (coefficientFunctorChainDegreeIso F R S e K) (by
      rintro i j (rfl : j + 1 = i)
      exact coefficientFunctorChainDegreeIso_comm F R S e K j)

/-- The chain comparison preserves every simplex summand. -/
@[reassoc (attr := simp)]
theorem coefficientFunctorChainsIso_ι (K : SSet.{w}) (n : ℕ) (x : K _⦋n⦌) :
    F.map (K.ιChainComplex (R := R) x) ≫
        (coefficientFunctorChainsIso F R S e K).hom.f n =
      e.hom ≫ K.ιChainComplex (R := S) x :=
  coefficientFunctorChainDegreeIso_ι F R S e K n x

/-- The actual chain comparison is natural under every simplicial map. -/
@[reassoc]
theorem coefficientFunctorChainsIso_hom_naturality {K L : SSet.{w}} (f : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (SSet.chainComplexMap f R) ≫
        (coefficientFunctorChainsIso F R S e L).hom =
      (coefficientFunctorChainsIso F R S e K).hom ≫ SSet.chainComplexMap f S := by
  ext n
  apply coefficientFunctorChain_hom_ext F R K n
  intro x
  change F.map (K.ιChainComplex (R := R) x) ≫
      (F.map ((SSet.chainComplexMap f R).f n) ≫
        (coefficientFunctorChainDegreeIso F R S e L n).hom) =
    F.map (K.ιChainComplex (R := R) x) ≫
      ((coefficientFunctorChainDegreeIso F R S e K n).hom ≫
        (SSet.chainComplexMap f S).f n)
  rw [← F.map_comp_assoc, SSet.ι_chainComplexMap_f,
    coefficientFunctorChainDegreeIso_ι, coefficientFunctorChainDegreeIso_ι_assoc,
    SSet.ι_chainComplexMap_f]

end CoefficientFunctor

/-- Rationalizing genuine integral singular chains gives the genuine singular
chain complex with rational coefficients. -/
def rationalSingularChainsIso (X : TopCat.{0}) :
    (RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (LocalHomology.Cycles.integralSingularChains X) ≅
      (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).obj X :=
  coefficientFunctorChainsIso RationalScalarExtension.Cycles.rationalizeModules (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ)
    RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.obj X)

/-- Rational coefficient comparison is natural for every continuous map. -/
@[reassoc]
theorem rationalSingularChainsIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫ (rationalSingularChainsIso Y).hom =
      (rationalSingularChainsIso X).hom ≫ (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f :=
  coefficientFunctorChainsIso_hom_naturality RationalScalarExtension.Cycles.rationalizeModules
    (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ) RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.map f)

/-- The rational chain comparison transports the coefficient of each singular
simplex by the canonical rationalized-unit isomorphism. -/
@[reassoc (attr := simp)]
theorem rationalSingularChainsIso_ι (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    RationalScalarExtension.Cycles.rationalizeModules.map
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
        (rationalSingularChainsIso X).hom.f n =
      RationalScalarExtension.Cycles.rationalizeUnitIso.hom ≫
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ :=
  coefficientFunctorChainsIso_ι RationalScalarExtension.Cycles.rationalizeModules
    (ModuleCat.of ℤ ℤ) (ModuleCat.of ℚ ℚ) RationalScalarExtension.Cycles.rationalizeUnitIso (TopCat.toSSet.obj X) n σ

/-- On an elementary tensor supported at a singular simplex, the coefficient
is the usual product of the rational scalar and the integral coefficient. -/
@[simp]
theorem rationalSingularChainsIso_hom_tmul_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (q : ℚ) (z : ℤ) :
    (rationalSingularChainsIso X).hom.f n
        (q ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ (q * (z : ℚ)) := by
  have h := ConcreteCategory.congr_hom (rationalSingularChainsIso_ι X n σ)
    (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)
  change (rationalSingularChainsIso X).hom.f n
      (RationalScalarExtension.Cycles.rationalizeModules.map
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)
        (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) =
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ
      (RationalScalarExtension.Cycles.rationalizeUnitIso.hom (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) at h
  rw [RationalScalarExtension.Cycles.rationalizeUnitIso_hom_tmul] at h
  exact h

/-- A unit-coefficient integral singular simplex becomes the same simplex
with unit rational coefficient. -/
@[simp]
theorem rationalSingularChainsIso_hom_one_tmul_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (rationalSingularChainsIso X).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ 1 := by
  simpa using rationalSingularChainsIso_hom_tmul_simplex X n σ 1 1

/-- The rational comparison assembled as a natural isomorphism of the actual
singular chain functors. -/
def rationalSingularChainsNatIso :
    LocalHomology.Cycles.integralSingularChainFunctor ⋙
        RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ :=
  NatIso.ofComponents rationalSingularChainsIso
    (fun f => rationalSingularChainsIso_hom_naturality f)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles
