import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismTotalCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientCochainCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Morphism Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCohomologyCup.Total

noncomputable section

/-! A product-preserving morphism after exact coefficient extension
preserves the original categorical Čech cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct.Cech

universe u v r s a b
variable {C : Type u} [Category.{v} C]
  {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  (F : ModuleCat.{a} R ⥤ ModuleCat.{b} S)
  [F.Additive] [F.PreservesHomology] [PreservesFiniteLimits F]
  (η : ∀ M : ModuleCat.{a} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{a} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{a} R) ℕ)

variable (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{b} S) ℕ)
  (f : GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P ⟶ Q)

def homologyMap (n : ℕ) := CoefficientCochainCup.map F η (Presheaf.TotalCup.CechProduct.total E P) (Presheaf.TotalCup.CechProduct.total E Q)
  (MorphismTotalCup.cochainMap F E hE P Q f) n

variable
  (μ : ∀ p q U, (P.X p).obj U →ₗ[R] (P.X q).obj U →ₗ[R] (P.X (p+q)).obj U)
  (ν : ∀ p q U, (Q.X p).obj U →ₗ[S] (Q.X q).obj U →ₗ[S] (Q.X (p+q)).obj U)
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p+q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p+q) (p+q+1)).app U (μ p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (p+1)+q=p+q+1) U (μ (p+1) q U ((P.d p (p+1)).app U x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast P (by omega : p+(q+1)=p+q+1) U
        (μ p (q+1) U x ((P.d q (q+1)).app U y)))
  (hν : ∀ p q {U V : Cᵒᵖ} (t : U ⟶ V) (x : (Q.X p).obj U) (y : (Q.X q).obj U),
    (Q.X (p+q)).map t (ν p q U x y) = ν p q V ((Q.X p).map t x) ((Q.X q).map t y))
  (dν : ∀ p q U (x : (Q.X p).obj U) (y : (Q.X q).obj U),
    (Q.d (p+q) (p+q+1)).app U (ν p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast Q (by omega : (p+1)+q=p+q+1) U (ν (p+1) q U ((Q.d p (p+1)).app U x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast Q (by omega : p+(q+1)=p+q+1) U
        (ν p (q+1) U x ((Q.d q (q+1)).app U y)))
  (hprod : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    (f.f (p+q)).app U (η ((P.X (p+q)).obj U) (μ p q U x y)) =
      ν p q U ((f.f p).app U (η ((P.X p).obj U) x))
        ((f.f q).app U (η ((P.X q).obj U) y)))

abbrev homologyMap_cup := CoefficientCochainCup.map_cup F η hη (Presheaf.TotalCup.CechProduct.total E P) (Presheaf.TotalCup.CechProduct.total E Q)
  (MorphismTotalCup.cochainMap F E hE P Q f)
  (Presheaf.TotalCup.CechProduct.totalCup E P μ) (Presheaf.TotalCup.CechProduct.totalCup E Q ν) (Presheaf.TotalLeibniz.CechProduct.differential_totalCup E P μ hμ dμ)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup E Q ν hν dν) (MorphismTotalCup.map_cup F η hη E hE P Q f μ ν hprod)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCohomologyCup.Total
