import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Homology Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomologyScalarExtension.ChainScalarExtension

noncomputable section

section

/-! Scalar extension of the actual singular chain complex along a coefficient ring homomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial TensorProduct ChangeOfRings

open OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S)

abbrev extension : ModuleCat.{0} R ⥤ ModuleCat.{0} S := ModuleCat.extendScalars σ

instance extension_additive : (extension σ).Additive where
  map_add {X Y f g} := by
    let : Module R S := Module.compHom S σ
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : S) ⊗ₜ[R, σ] ((f + g) x) =
      (1 : S) ⊗ₜ[R, σ] f x + (1 : S) ⊗ₜ[R, σ] g x
    exact TensorProduct.tmul_add _ _ _

def unitIso : (extension σ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI : Algebra R S := σ.toAlgebra
  letI : Module R S := Module.compHom S σ
  letI : SMul R S := (Module.compHom S σ).toSMul
  letI : IsScalarTower R S S := IsScalarTower.of_compHom R S S
  letI : SMulCommClass R S S := SMulCommClass.of_commMonoid R S S
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

theorem unitIso_tmul (s : S) (r : R) :
    (unitIso σ).hom (s ⊗ₜ[R, σ] r) = s * σ r := by
  change σ r * s = s * σ r
  exact mul_comm _ _

def chainsIso (X : TopCat.{0}) :
    ((extension σ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) ≅ AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := S) X :=
  AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.coefficientFunctorChainsIso (extension σ) (ModuleCat.of R R) (ModuleCat.of S S)
    (unitIso σ) (TopCat.toSSet.obj X)

theorem chainsIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    ((extension σ).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) ≫ (chainsIso σ Y).hom =
      (chainsIso σ X).hom ≫ AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := S) f :=
  AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.coefficientFunctorChainsIso_hom_naturality (extension σ)
    (ModuleCat.of R R) (ModuleCat.of S S) (unitIso σ) (TopCat.toSSet.map f)

end

/-! Exact coefficient extension identifies the actual singular homology objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable {R S : Type} [Field R] [Field S] (σ : R →+* S)

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension σ) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.Flat.of_isField (Field.toIsField R) σ)

theorem compose_squares {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ F) (e : F ⟶ D)
    (f : F ⟶ G) (g : G ⟶ E) (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) :
    a ≫ b ≫ c = (d ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

def homologyIso (X : TopCat.{0}) (n : ℕ) :
    (extension σ).obj ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) ≅
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := S) X).homology n :=
  ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).sc n |>.mapHomologyIso (extension σ)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).mapIso (chainsIso σ X)

theorem homologyIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (extension σ).map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) n) ≫
      (homologyIso σ Y n).hom = (homologyIso σ X n).hom ≫
        HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := S) f) n := by
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f)) (extension σ)
  have h₂ := congrArg ((HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).map)
    (chainsIso_naturality σ f)
  simp only [Functor.map_comp] at h₂
  exact compose_squares _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomologyScalarExtension.ChainScalarExtension
