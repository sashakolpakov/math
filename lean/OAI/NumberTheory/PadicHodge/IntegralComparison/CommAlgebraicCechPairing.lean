import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCup
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Comm Algebraic Cech Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechPairing

noncomputable section

/-! The canonical algebra-to-module Čech comparison preserves the
literal section multiplication and the Alexander–Whitney product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]

abbrev forgetModule : CommAlgCat.{t} R ⥤ ModuleCat.{t} R :=
  forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

def modulePresheaf (P : Cᵒᵖ ⥤ CommAlgCat.{t} R) := P ⋙ forgetModule.{t, r}

def multiplication (P : Cᵒᵖ ⥤ CommAlgCat.{t} R) (U : Cᵒᵖ) :
    (modulePresheaf P).obj U →ₗ[R] (modulePresheaf P).obj U →ₗ[R] (modulePresheaf P).obj U :=
  LinearMap.mul R (P.obj U)

theorem multiplication_natural (P : Cᵒᵖ ⥤ CommAlgCat.{t} R)
    {U V : Cᵒᵖ} (α : U ⟶ V) (x y : (modulePresheaf P).obj U) :
    (modulePresheaf P).map α (multiplication P U x y) =
      multiplication P V ((modulePresheaf P).map α x) ((modulePresheaf P).map α y) :=
  map_mul (P.map α).hom (show P.obj U from x) (show P.obj U from y)

variable [HasProducts.{w} (CommAlgCat.{max w t} R)]
  [PreservesLimitsOfSize.{w, w} (forgetModule.{max w t, r} (R := R))]
  (N : SimplicialObject (FormalCoproduct.{w} C)) (P : Cᵒᵖ ⥤ CommAlgCat.{max w t} R)

local instance moduleProducts : HasProducts.{w} (ModuleCat.{max w t} R) :=
  fun T => (ModuleCat.hasLimitsOfSize.{w, w, max w t, r}).has_limits_of_shape (Discrete T)

def algebraObject := (FormalCoproduct.cosimplicialObjectFunctor N).obj P
def comparison := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso (forgetModule.{max w t, r}) N P

theorem projection_comparison (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (algebraObject.{u, v, w, t, r} N P).obj n) :
    Cech.BilinearPairing.projection N (modulePresheaf.{u, v, max w t, r} P) n i ((comparison.{u, v, w, t, r} N P).hom.app n x) =
      (Pi.π (fun j => P.obj (op ((N.obj (op n)).obj j))) i).hom x :=
  ConcreteCategory.congr_hom (piComparison_comp_π (forgetModule.{max w t, r})
    (fun j => P.obj (op ((N.obj (op n)).obj j))) i) x

theorem comparison_mul (n : SimplexCategory) (x y : (algebraObject.{u, v, w, t, r} N P).obj n) :
    (comparison.{u, v, w, t, r} N P).hom.app n (x * y) =
      Cech.BilinearPairing.pairing N (modulePresheaf.{u, v, max w t, r} P) (modulePresheaf.{u, v, max w t, r} P) (modulePresheaf.{u, v, max w t, r} P)
        (multiplication.{u, v, max w t, r} P) n ((comparison.{u, v, w, t, r} N P).hom.app n x) ((comparison.{u, v, w, t, r} N P).hom.app n y) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => (modulePresheaf.{u, v, max w t, r} P).obj (op ((N.obj (op n)).obj i)))
  intro i
  change Cech.BilinearPairing.projection N (modulePresheaf.{u, v, max w t, r} P) n i _ =
    Cech.BilinearPairing.projection N (modulePresheaf.{u, v, max w t, r} P) n i _
  erw [Cech.BilinearPairing.projection_pairing, projection_comparison,
    projection_comparison, projection_comparison]
  exact map_mul (Pi.π (fun j => P.obj (op ((N.obj (op n)).obj j))) i).hom x y

def complexIso : Cosimplicial.ModuleComplex.complex (algebraObject.{u, v, w, t, r} N P) ≅
    Presheaf.AugmentationProduct.source N (modulePresheaf.{u, v, max w t, r} P) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{max w t} R)).mapIso
    (comparison.{u, v, w, t, r} N P)

theorem cochain_cup (p q : ℕ) (x : (algebraObject.{u, v, w, t, r} N P).obj ⦋p⦌)
    (y : (algebraObject.{u, v, w, t, r} N P).obj ⦋q⦌) :
    (complexIso.{u, v, w, t, r} N P).hom.f (p + q)
      (Cosimplicial.Cup.cup (Cosimplicial.ModuleComplex.ringObject (algebraObject.{u, v, w, t, r} N P)) x y) =
        Presheaf.AugmentationProduct.sourceCup N (modulePresheaf.{u, v, max w t, r} P) (multiplication.{u, v, max w t, r} P) p q
          ((complexIso.{u, v, w, t, r} N P).hom.f p x) ((complexIso.{u, v, w, t, r} N P).hom.f q y) := by
  change (comparison.{u, v, w, t, r} N P).hom.app ⦋p + q⦌
    (((algebraObject.{u, v, w, t, r} N P).map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x) *
      ((algebraObject.{u, v, w, t, r} N P).map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y)) =
    Cech.BilinearPairing.pairing N (modulePresheaf.{u, v, max w t, r} P)
      (modulePresheaf.{u, v, max w t, r} P) (modulePresheaf.{u, v, max w t, r} P)
      (multiplication.{u, v, max w t, r} P) ⦋p + q⦌
      ((Cech.BilinearPairing.cosimplicial N (modulePresheaf.{u, v, max w t, r} P)).map
        (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) ((comparison.{u, v, w, t, r} N P).hom.app ⦋p⦌ x))
      ((Cech.BilinearPairing.cosimplicial N (modulePresheaf.{u, v, max w t, r} P)).map
        (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) ((comparison.{u, v, w, t, r} N P).hom.app ⦋q⦌ y))
  have h₁ := ConcreteCategory.congr_hom ((comparison.{u, v, w, t, r} N P).hom.naturality (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)) x
  have h₂ := ConcreteCategory.congr_hom ((comparison.{u, v, w, t, r} N P).hom.naturality (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)) y
  exact (comparison_mul.{u, v, w, t, r} N P ⦋p + q⦌
    ((algebraObject.{u, v, w, t, r} N P).map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x)
    ((algebraObject.{u, v, w, t, r} N P).map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y)).trans
    (congrArg₂ (fun a b : (Cech.BilinearPairing.cosimplicial N
      (modulePresheaf.{u, v, max w t, r} P)).obj ⦋p + q⦌ =>
      Cech.BilinearPairing.pairing N (modulePresheaf.{u, v, max w t, r} P)
        (modulePresheaf.{u, v, max w t, r} P) (modulePresheaf.{u, v, max w t, r} P)
        (multiplication.{u, v, max w t, r} P) ⦋p + q⦌ a b) h₁ h₂)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechPairing
