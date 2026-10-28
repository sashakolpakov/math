import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Augmentation Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationCohomology.Product

noncomputable section

/-! The coefficient Čech product and its augmentation on the original
categorical cohomology groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (A : Cᵒᵖ ⥤ ModuleCat.{max w t} R)

theorem source_d_apply (n : ℕ) (x : (AugmentationProduct.source N A).X n) :
    (AugmentationProduct.source N A).d n (n + 1) x =
      Cosimplicial.BilinearCup.differential (Cech.BilinearPairing.cosimplicial N A) n x :=
  Cosimplicial.BilinearCup.complex_d_apply (Cech.BilinearPairing.cosimplicial N A) n x

theorem source_degreeCast {n m : ℕ} (h : n = m) (x : (AugmentationProduct.source N A).X n) :
    Cochain.CohomologyCup.degreeCast (AugmentationProduct.source N A) h x =
      Cosimplicial.BilinearDegrees.Cup.degreeCast (Cech.BilinearPairing.cosimplicial N A) h x := by
  subst m
  rfl

variable (a : ∀ U : Cᵒᵖ, A.obj U →ₗ[R] A.obj U →ₗ[R] A.obj U)
  (ha : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x y : A.obj U),
    A.map f (a U x y) = a V (A.map f x) (A.map f y))

include ha in
theorem source_differential_cup (n m : ℕ) (x : (AugmentationProduct.source N A).X n) (y : (AugmentationProduct.source N A).X m) :
    (AugmentationProduct.source N A).d (n + m) (n + m + 1) (AugmentationProduct.sourceCup N A a n m x y) =
      Cochain.CohomologyCup.cupInto (AugmentationProduct.source N A) (AugmentationProduct.sourceCup N A a)
        (n + 1) m (n + m + 1) (by omega) ((AugmentationProduct.source N A).d n (n + 1) x) y +
      (-1 : ℤ) ^ n • Cochain.CohomologyCup.cupInto (AugmentationProduct.source N A) (AugmentationProduct.sourceCup N A a)
        n (m + 1) (n + m + 1) (by omega) x ((AugmentationProduct.source N A).d m (m + 1) y) := by
  simp only [Cochain.CohomologyCup.cupInto, source_d_apply]
  exact Cosimplicial.BilinearDegrees.Cup.differential_cup_cast _ _ _
    (Cech.BilinearPairing.pairing N A A A a)
    (Cech.BilinearPairing.pairing_natural N A A A a ha) n m x y

def sourceCohomologyCup (n m : ℕ) :
    (AugmentationProduct.source N A).homology n →ₗ[R] (AugmentationProduct.source N A).homology m →ₗ[R] (AugmentationProduct.source N A).homology (n + m) :=
  Cochain.CohomologyCup.cohomologyCup (AugmentationProduct.source N A) (AugmentationProduct.sourceCup N A a)
    (source_differential_cup N A a ha) n m

variable (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (ι : A ⟶ P.X 0) (hι : ι ≫ P.d 0 1 = 0)
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p + q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p + q) (p + q + 1)).app U (μ p q U x y) =
      CechProduct.sectionDegreeCast P (by omega : (p + 1) + q = p + q + 1) U
        (μ (p + 1) q U ((P.d p (p + 1)).app U x) y) +
      (-1 : ℤ) ^ p • CechProduct.sectionDegreeCast P
        (by omega : p + (q + 1) = p + q + 1) U
        (μ p (q + 1) U x ((P.d q (q + 1)).app U y)))
  (hmul : ∀ U (x y : A.obj U), ι.app U (a U x y) = μ 0 0 U (ι.app U x) (ι.app U y))

include hmul in
theorem cohomologyMap_cup (n m : ℕ) (x : (AugmentationProduct.source N A).homology n) (y : (AugmentationProduct.source N A).homology m) :
    HomologicalComplex.homologyMap (AugmentationProduct.map N P A ι hι) (n + m) (sourceCohomologyCup N A a ha n m x y) =
      CohomologyProduct.Cech.cohomologyCup N P μ hμ dμ n m
        (HomologicalComplex.homologyMap (AugmentationProduct.map N P A ι hι) n x)
        (HomologicalComplex.homologyMap (AugmentationProduct.map N P A ι hι) m y) :=
  Cochain.CupNaturality.Cohomology.cohomologyMap_cup (AugmentationProduct.sourceCup N A a) (TotalCup.CechProduct.totalCup N P μ)
    (source_differential_cup N A a ha) (TotalLeibniz.CechProduct.differential_totalCup N P μ hμ dμ)
    (AugmentationProduct.map N P A ι hι) (AugmentationProduct.map_cup N P A ι hι μ a hmul) n m x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationCohomology.Product
