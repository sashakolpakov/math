import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalComponents
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality

/-! # Augmentation Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct

noncomputable section

/-! The actual augmentation from a coefficient presheaf into a complex
induces a product-preserving map from its Čech complex to the total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalComponents.CechProduct

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (A : Cᵒᵖ ⥤ ModuleCat.{max w t} R) (ι : A ⟶ P.X 0)
  (hι : ι ≫ P.d 0 1 = 0)

def source : CochainComplex (ModuleCat.{max w t} R) ℕ :=
  (FormalCoproduct.cochainComplexFunctor N).obj A

def rowMap : source N A ⟶ (TotalCup.CechProduct.bicomplex N P).X 0 :=
  (FormalCoproduct.cochainComplexFunctor N).map ι

include hι in
theorem rowMap_closed (n : ℕ) (x : (source N A).X n) :
    (CechDifferential.Product.presheafDifferential N P 0).app ⦋n⦌ ((rowMap N P A ι).f n x) = 0 := by
  have h : rowMap N P A ι ≫ (TotalCup.CechProduct.bicomplex N P).d 0 1 = 0 := by
    change (FormalCoproduct.cochainComplexFunctor N).map ι ≫
      (FormalCoproduct.cochainComplexFunctor N).map (P.d 0 1) = 0
    rw [← Functor.map_comp, hι, Functor.map_zero]
  exact ConcreteCategory.congr_hom
    (congrArg (fun e : source N A ⟶ (TotalCup.CechProduct.bicomplex N P).X 1 => e.f n) h) x

def componentMap (n : ℕ) : (source N A).X n ⟶ (TotalCup.CechProduct.total N P).X n :=
  (rowMap N P A ι).f n ≫ (TotalCup.CechProduct.bicomplex N P).ιTotal (.up ℕ) 0 n n (Nat.zero_add n)

include hι in
theorem componentMap_comm (n : ℕ) :
    (source N A).d n (n + 1) ≫ componentMap N P A ι (n + 1) =
      componentMap N P A ι n ≫ (TotalCup.CechProduct.total N P).d n (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := TotalComponents.CechProduct.differential_component N P 0 n n (Nat.zero_add n) ((rowMap N P A ι).f n x)
  rw [rowMap_closed N P A ι hι, map_zero, pow_zero, one_smul, zero_add] at h
  have hn := ConcreteCategory.congr_hom ((rowMap N P A ι).comm n (n + 1)).symm x
  change (rowMap N P A ι).f (n + 1) ((source N A).d n (n + 1) x) =
    ((TotalCup.CechProduct.bicomplex N P).X 0).d n (n + 1) ((rowMap N P A ι).f n x) at hn
  rw [TotalCup.CechProduct.bicomplex_d_cech_apply] at hn
  exact (congrArg (TotalComponents.CechProduct.component N P 0 (n + 1) (n + 1) (Nat.zero_add (n + 1))) hn).trans h.symm

def map : source N A ⟶ TotalCup.CechProduct.total N P where
  f := componentMap N P A ι
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    exact (componentMap_comm N P A ι hι i).symm

theorem map_apply (n : ℕ) (x : (source N A).X n) :
    (AugmentationProduct.map N P A ι hι).f n x = TotalComponents.CechProduct.component N P 0 n n (Nat.zero_add n) ((rowMap N P A ι).f n x) := rfl

variable (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)
  (a : ∀ U : Cᵒᵖ, A.obj U →ₗ[R] A.obj U →ₗ[R] A.obj U)

def sourceCup (n m : ℕ) : (source N A).X n →ₗ[R] (source N A).X m →ₗ[R]
    (source N A).X (n + m) :=
  Cosimplicial.BilinearCup.cup (Cech.BilinearPairing.cosimplicial N A)
    (Cech.BilinearPairing.cosimplicial N A) (Cech.BilinearPairing.cosimplicial N A)
    (Cech.BilinearPairing.pairing N A A A a) n m

variable (hmul : ∀ U (x y : A.obj U), ι.app U (a U x y) = μ 0 0 U (ι.app U x) (ι.app U y))

include hmul in
theorem rowMap_cup (n m : ℕ) (x : (source N A).X n) (y : (source N A).X m) :
    (rowMap N P A ι).f (n + m) (sourceCup N A a n m x y) =
      CechProduct.cup N P μ 0 0 n m ((rowMap N P A ι).f n x) ((rowMap N P A ι).f m y) :=
  Cech.PairingNaturality.Bilinear.cup_coefficient_natural N a (μ 0 0) ι ι ι hmul n m x y

include hmul in
theorem map_cup (n m : ℕ) (x : (source N A).X n) (y : (source N A).X m) :
    (AugmentationProduct.map N P A ι hι).f (n + m) (sourceCup N A a n m x y) =
      TotalCup.CechProduct.totalCup N P μ n m ((AugmentationProduct.map N P A ι hι).f n x) ((AugmentationProduct.map N P A ι hι).f m y) := by
  have h := TotalCup.CechProduct.totalCup_ι N P μ n m 0 n 0 m (Nat.zero_add n) (Nat.zero_add m)
    ((rowMap N P A ι).f n x) ((rowMap N P A ι).f m y)
  simp only [mul_zero, pow_zero, one_smul] at h
  exact (congrArg (TotalComponents.CechProduct.component N P 0 (n + m) (n + m) (Nat.zero_add (n + m)))
    (rowMap_cup N P A ι μ a hmul n m x y)).trans h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct
