import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafComplexProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.CochainMap

/-! # Cone Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct

noncomputable section

/-! Constant-presheaf cochain maps retain their products through the
actual crystalline coefficient lift and sheafification unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {D : Type v} [Category.{w} D] (B : Type u) [CommRing B]
  (J : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))]
  [(J.W (A := ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))).IsMonoidal]
  (M : CochainComplex (ModuleCat.{u} B) ℕ)
  (P : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} B) ℕ)
  (a : ((Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

def coefficientSource : CochainComplex (ModuleCat.{u + 1} CR) ℕ :=
  ((T).mapHomologicalComplex (.up ℕ)).obj M

def coefficientMap :
    ((Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ)).obj (coefficientSource B M) ⟶
      SheafComplexProduct.coefficientComplex B P :=
   Constant.CochainMap.map (T) M P a

def map :
    ((Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ)).obj (coefficientSource B M) ⟶
      SheafComplexProduct.underlyingComplex.{u,v,w} B J P :=
  coefficientMap B M P a ≫ Sheafified.CochainUnit.Pairing.unit.{v,w,u + 1} J CR
    (SheafComplexProduct.coefficientComplex B P)

variable (μ : ∀ i j V, (P.X i).obj V →ₗ[B] (P.X j).obj V →ₗ[B] (P.X (i+j)).obj V)
  (hμ : ∀ i j {V W : Dᵒᵖ} (f : V ⟶ W) x y,
    (P.X (i+j)).map f (μ i j V x y) = μ i j W ((P.X i).map f x) ((P.X j).map f y))
  (σ : ∀ i j, M.X i →ₗ[B] M.X j →ₗ[B] M.X (i+j))
  (ha : ∀ i j V x y, (a.f (i+j)).app V (σ i j x y) =
    μ i j V ((a.f i).app V x) ((a.f j).app V y))

def sourcePairing (i j : ℕ) :=
  CoefficientPairing.lift B (M.X i) (M.X j) (M.X (i+j)) (σ i j)

include ha in
theorem coefficientMap_pairing (i j : ℕ) (V : Dᵒᵖ)
    (x : (coefficientSource B M).X i) (y : (coefficientSource B M).X j) :
    ((coefficientMap B M P a).f (i+j)).app V (sourcePairing B M σ i j x y) =
      SheafComplexProduct.coefficientPairing B P μ i j V
        (((coefficientMap B M P a).f i).app V x)
        (((coefficientMap B M P a).f j).app V y) :=
  CoefficientPairing.map_lift B _ _ _ ((a.f i).app V)
    ((a.f j).app V) ((a.f (i+j)).app V) (σ i j) (μ i j V) (ha i j V) x y

include ha in
theorem map_pairing (i j : ℕ) (V : Dᵒᵖ)
    (x : (coefficientSource B M).X i) (y : (coefficientSource B M).X j) :
    ((ConeProduct.map B J M P a).f (i+j)).app V (sourcePairing B M σ i j x y) =
      SheafComplexProduct.sectionPairing.{u,v,w} B J P μ hμ i j V
        (((ConeProduct.map B J M P a).f i).app V x) (((ConeProduct.map B J M P a).f j).app V y) :=
  (congrArg
    (((Sheafified.CochainUnit.Pairing.unit.{v,w,u + 1} J CR
      (SheafComplexProduct.coefficientComplex B P)).f (i+j)).app V)
    (coefficientMap_pairing B M P a μ σ ha i j V x y)).trans
    (SheafComplexProduct.unit_pairing B J P μ hμ i j V _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct
