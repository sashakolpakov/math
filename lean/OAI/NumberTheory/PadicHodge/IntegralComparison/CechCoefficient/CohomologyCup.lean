import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientCochainCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.CohomologyCup.Total

noncomputable section

/-! The genuine exact coefficient comparison for finite Čech totals
preserves their original categorical cohomology cup product. -/

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

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P

def homologyMap (n : ℕ) := CoefficientCochainCup.map F η (Presheaf.TotalCup.CechProduct.total E P) (Presheaf.TotalCup.CechProduct.total E Q)
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom n

variable
  (μ : ∀ p q U, (P.X p).obj U →ₗ[R] (P.X q).obj U →ₗ[R] (P.X (p+q)).obj U)
  (ν : ∀ p q U, F.obj ((P.X p).obj U) →ₗ[S] F.obj ((P.X q).obj U) →ₗ[S]
    F.obj ((P.X (p+q)).obj U))
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p+q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p+q) (p+q+1)).app U (μ p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (p+1)+q=p+q+1) U (μ (p+1) q U ((P.d p (p+1)).app U x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast P (by omega : p+(q+1)=p+q+1) U
        (μ p (q+1) U x ((P.d q (q+1)).app U y)))
  (hν : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.obj ((P.X p).obj U)) (y : F.obj ((P.X q).obj U)),
    F.map ((P.X (p+q)).map f) (ν p q U x y) =
      ν p q V (F.map ((P.X p).map f) x) (F.map ((P.X q).map f) y))
  (dν : ∀ p q U (x : F.obj ((P.X p).obj U)) (y : F.obj ((P.X q).obj U)),
    F.map ((P.d (p+q) (p+q+1)).app U) (ν p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P)
        (by omega : (p+1)+q=p+q+1) U (ν (p+1) q U (F.map ((P.d p (p+1)).app U) x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P)
        (by omega : p+(q+1)=p+q+1) U (ν p (q+1) U x (F.map ((P.d q (q+1)).app U) y)))
  (hprod : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    η ((P.X (p+q)).obj U) (μ p q U x y) =
      ν p q U (η ((P.X p).obj U) x) (η ((P.X q).obj U) y))

abbrev homologyMap_cup := CoefficientCochainCup.map_cup F η hη (Presheaf.TotalCup.CechProduct.total E P) (Presheaf.TotalCup.CechProduct.total E Q)
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom
  (Presheaf.TotalCup.CechProduct.totalCup E P μ) (Presheaf.TotalCup.CechProduct.totalCup E Q ν) (Presheaf.TotalLeibniz.CechProduct.differential_totalCup E P μ hμ dμ)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup E Q ν hν dν) (TotalCup.map_cup F η hη E hE P μ ν hprod)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.CohomologyCup.Total
