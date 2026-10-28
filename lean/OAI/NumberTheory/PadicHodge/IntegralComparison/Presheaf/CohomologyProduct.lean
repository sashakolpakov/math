import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality

/-! # Cohomology Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct.Cech

noncomputable section

/-! The native Čech total product induces a product on the original
categorical cohomology, naturally in product-preserving cochain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p + q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p + q) (p + q + 1)).app U (μ p q U x y) =
      CechProduct.sectionDegreeCast P (by omega : (p + 1) + q = p + q + 1) U
        (μ (p + 1) q U ((P.d p (p + 1)).app U x) y) +
      (-1 : ℤ) ^ p • CechProduct.sectionDegreeCast P (by omega : p + (q + 1) = p + q + 1) U
        (μ p (q + 1) U x ((P.d q (q + 1)).app U y)))

def cohomologyCup (p q : ℕ) :
    (TotalCup.CechProduct.total N P).homology p →ₗ[R] (TotalCup.CechProduct.total N P).homology q →ₗ[R] (TotalCup.CechProduct.total N P).homology (p + q) :=
  Cochain.CohomologyCup.cohomologyCup (TotalCup.CechProduct.total N P) (TotalCup.CechProduct.totalCup N P μ)
    (TotalLeibniz.CechProduct.differential_totalCup N P μ hμ dμ) p q

variable
  (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (ν : ∀ p q (U : Cᵒᵖ), (Q.X p).obj U →ₗ[R]
    (Q.X q).obj U →ₗ[R] (Q.X (p + q)).obj U)
  (hν : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (Q.X p).obj U) (y : (Q.X q).obj U),
    (Q.X (p + q)).map f (ν p q U x y) = ν p q V ((Q.X p).map f x) ((Q.X q).map f y))
  (dν : ∀ p q (U : Cᵒᵖ) (x : (Q.X p).obj U) (y : (Q.X q).obj U),
    (Q.d (p + q) (p + q + 1)).app U (ν p q U x y) =
      CechProduct.sectionDegreeCast Q (by omega : (p + 1) + q = p + q + 1) U
        (ν (p + 1) q U ((Q.d p (p + 1)).app U x) y) +
      (-1 : ℤ) ^ p • CechProduct.sectionDegreeCast Q (by omega : p + (q + 1) = p + q + 1) U
        (ν p (q + 1) U x ((Q.d q (q + 1)).app U y)))
  (f : P ⟶ Q)
  (hf : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (f.f (p + q)).app U (μ p q U x y) = ν p q U ((f.f p).app U x) ((f.f q).app U y))

include hf in
theorem totalMap_cohomologyCup (p q : ℕ)
    (x : (TotalCup.CechProduct.total N P).homology p) (y : (TotalCup.CechProduct.total N P).homology q) :
    HomologicalComplex.homologyMap (CechProductNaturality.totalMap N f) (p + q) (cohomologyCup N P μ hμ dμ p q x y) =
      cohomologyCup N Q ν hν dν p q
        (HomologicalComplex.homologyMap (CechProductNaturality.totalMap N f) p x)
        (HomologicalComplex.homologyMap (CechProductNaturality.totalMap N f) q y) :=
  Cochain.CupNaturality.Cohomology.cohomologyMap_cup (TotalCup.CechProduct.totalCup N P μ) (TotalCup.CechProduct.totalCup N Q ν)
    (TotalLeibniz.CechProduct.differential_totalCup N P μ hμ dμ) (TotalLeibniz.CechProduct.differential_totalCup N Q ν hν dν)
    (CechProductNaturality.totalMap N f) (CechProductNaturality.totalMap_pairing N μ ν f hf) p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct.Cech
