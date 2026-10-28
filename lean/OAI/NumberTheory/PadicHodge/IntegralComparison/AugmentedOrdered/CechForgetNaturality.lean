import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProjectionNaturality
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cech Forget Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

noncomputable section

/-! Changing the actual coefficient complex commutes with forgetting
support in the augmented ordered Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem projection_square {D : Type*} [Category D]
    {T₁ T₂ C₁ C₂ A₁ A₂ : D} {t : T₁ ⟶ T₂} {p₁ : T₁ ⟶ C₁} {p₂ : T₂ ⟶ C₂}
    {a : C₁ ⟶ C₂} {z₁ : C₁ ⟶ A₁} {z₂ : C₂ ⟶ A₂} {b : A₁ ⟶ A₂}
    (ht : t ≫ p₂ = p₁ ≫ a) (hz : a ≫ z₂ = z₁ ≫ b) :
    t ≫ (p₂ ≫ z₂) = (p₁ ≫ z₁) ≫ b := by
  rw [← Category.assoc, ht, Category.assoc, hz, ← Category.assoc]

open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A]
  {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ}
  [(CechFunctor.bicomplex U K).HasTotal (.up ℕ)] [(CechFunctor.bicomplex U L).HasTotal (.up ℕ)]

def bicomplexMap (a : K ⟶ L) : CechFunctor.bicomplex U K ⟶ CechFunctor.bicomplex U L :=
  ((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map a

def map (a : K ⟶ L) : (CechFunctor.bicomplex U K).total (.up ℕ) ⟶ (CechFunctor.bicomplex U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U a) (.up ℕ)

def ambientMap (a : K ⟶ L) : CechForget.ambientComplex K ⟶ CechForget.ambientComplex L :=
  (((CategoryTheory.evaluation Cᵒᵖ A).obj (op (⊤_ C))).mapHomologicalComplex (.up ℕ)).map a

theorem comparison (a : K ⟶ L) :
    CechForgetNaturality.map U a ≫ CechForget.forgetSupport U L = CechForget.forgetSupport U K ≫ ambientMap a := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (HomologicalComplex₂.total.map (bicomplexMap U a) (.up ℕ)).f n ≫
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U L)) n 0 n ≫ (CechZero.zeroIso U (L.X n)).hom) =
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫ (CechZero.zeroIso U (K.X n)).hom) ≫
      (a.f n).app (op (⊤_ C))
  exact projection_square (TotalProjectionNaturality.map (bicomplexMap U a) n 0 n)
    (CechZero.zeroIso_naturality U (K.X n) (a.f n))

theorem homology (a : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (CechForgetNaturality.map U a) n ≫
      HomologicalComplex.homologyMap (CechForget.forgetSupport U L) n =
    HomologicalComplex.homologyMap (CechForget.forgetSupport U K) n ≫
      HomologicalComplex.homologyMap (ambientMap a) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (comparison U a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
