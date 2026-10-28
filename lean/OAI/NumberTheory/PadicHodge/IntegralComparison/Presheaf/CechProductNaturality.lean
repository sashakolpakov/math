import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairingNaturality

/-! # Cech Product Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality

noncomputable section

/-! Maps of the given presheaf complexes that preserve their local
products preserve the product on the actual Čech total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  {P Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ}
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)
  (ν : ∀ p q (U : Cᵒᵖ), (Q.X p).obj U →ₗ[R]
    (Q.X q).obj U →ₗ[R] (Q.X (p + q)).obj U)
  (f : P ⟶ Q)

def bicomplexMap : TotalCup.CechProduct.bicomplex N P ⟶ TotalCup.CechProduct.bicomplex N Q :=
  ((FormalCoproduct.cochainComplexFunctor N).mapHomologicalComplex (.up ℕ)).map f

def totalMap : TotalCup.CechProduct.total N P ⟶ TotalCup.CechProduct.total N Q := HomologicalComplex₂.total.map (bicomplexMap N f) (.up ℕ)

variable (hf : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
  (f.f (p + q)).app U (μ p q U x y) = ν p q U ((f.f p).app U x) ((f.f q).app U y))

include hf in
theorem bicomplexMap_pairing (p a q b : ℕ)
    (x : ((TotalCup.CechProduct.bicomplex N P).X p).X a) (y : ((TotalCup.CechProduct.bicomplex N P).X q).X b) :
    ((bicomplexMap N f).f (p + q)).f (a + b) (TotalCup.CechProduct.signedPairing N P μ p a q b x y) =
      TotalCup.CechProduct.signedPairing N Q ν p a q b (((bicomplexMap N f).f p).f a x)
        (((bicomplexMap N f).f q).f b y) := by
  have h := Cech.PairingNaturality.Bilinear.cup_coefficient_natural N (μ p q) (ν p q)
    (f.f p) (f.f q) (f.f (p + q)) (hf p q) a b x y
  change ((bicomplexMap N f).f (p + q)).f (a + b)
    ((-1 : ℤ) ^ (a * q) • CechProduct.cup N P μ p q a b x y) =
      (-1 : ℤ) ^ (a * q) • CechProduct.cup N Q ν p q a b
        (((bicomplexMap N f).f p).f a x) (((bicomplexMap N f).f q).f b y)
  exact (map_zsmul (((bicomplexMap N f).f (p + q)).f (a + b)).hom ((-1 : ℤ) ^ (a * q))
    (CechProduct.cup N P μ p q a b x y)).trans (congrArg ((-1 : ℤ) ^ (a * q) • ·) h)

include hf in
theorem totalMap_pairing (n m : ℕ) (x : (TotalCup.CechProduct.total N P).X n) (y : (TotalCup.CechProduct.total N P).X m) :
    (totalMap N f).f (n + m) (TotalCup.CechProduct.totalCup N P μ n m x y) =
      TotalCup.CechProduct.totalCup N Q ν n m ((totalMap N f).f n x) ((totalMap N f).f m y) :=
  BicomplexPairingNaturality.totalPairing_natural (TotalCup.CechProduct.signedPairing N P μ) (TotalCup.CechProduct.signedPairing N Q ν)
    (bicomplexMap N f) (bicomplexMap N f) (bicomplexMap N f)
    (bicomplexMap_pairing N μ ν f hf) n m x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality
