import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing

/-! # Pairing Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality

noncomputable section

/-! Coefficient maps preserving a bilinear presheaf pairing preserve
the induced native Čech pairing and Alexander–Whitney product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CosimplicialBilinearCup

universe u v

variable {R : Type u} [CommRing R]
  {A B C A' B' C' : CosimplicialObject (ModuleCat.{v} R)}
  (μ : ∀ n, A.obj n →ₗ[R] B.obj n →ₗ[R] C.obj n)
  (ν : ∀ n, A'.obj n →ₗ[R] B'.obj n →ₗ[R] C'.obj n)
  (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')

theorem cup_natural
    (hc : ∀ n (x : A.obj n) (y : B.obj n), h.app n (μ n x y) = ν n (f.app n x) (g.app n y))
    (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌) :
    h.app ⦋p + q⦌ (Cosimplicial.BilinearCup.cup A B C μ p q x y) = Cosimplicial.BilinearCup.cup A' B' C' ν p q (f.app ⦋p⦌ x) (g.app ⦋q⦌ y) := by
  have hf := ConcreteCategory.congr_hom (f.naturality (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)) x
  have hg := ConcreteCategory.congr_hom (g.naturality (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)) y
  exact (hc ⦋p + q⦌ _ _).trans (congrArg₂ (fun s t => ν ⦋p + q⦌ s t) hf hg)

end CosimplicialBilinearCup

namespace Bilinear

universe u v w t r

variable {R : Type r} [CommRing R] {D : Type u} [Category.{v} D]
  (N : SimplicialObject (FormalCoproduct.{w} D))
  {P Q T P' Q' T' : Dᵒᵖ ⥤ ModuleCat.{max w t} R}

def coefficientMap (f : P ⟶ P') : BilinearPairing.cosimplicial N P ⟶ BilinearPairing.cosimplicial N P' :=
  (FormalCoproduct.cosimplicialObjectFunctor N).map f

theorem projection_coefficientMap (f : P ⟶ P') (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (BilinearPairing.cosimplicial N P).obj n) :
    BilinearPairing.projection N P' n i ((coefficientMap N f).app n x) =
      f.app (op ((N.obj (op n)).obj i)) (BilinearPairing.projection N P n i x) :=
  ConcreteCategory.congr_hom (Pi.map_π (fun j => f.app (op ((N.obj (op n)).obj j))) i) x

variable (μ : ∀ U, P.obj U →ₗ[R] Q.obj U →ₗ[R] T.obj U)
  (ν : ∀ U, P'.obj U →ₗ[R] Q'.obj U →ₗ[R] T'.obj U)
  (f : P ⟶ P') (g : Q ⟶ Q') (h : T ⟶ T')

theorem pairing_coefficient_natural
    (hc : ∀ U (x : P.obj U) (y : Q.obj U), h.app U (μ U x y) = ν U (f.app U x) (g.app U y))
    (n : SimplexCategory) (x : (BilinearPairing.cosimplicial N P).obj n) (y : (BilinearPairing.cosimplicial N Q).obj n) :
    (coefficientMap N h).app n (BilinearPairing.pairing N P Q T μ n x y) =
      BilinearPairing.pairing N P' Q' T' ν n ((coefficientMap N f).app n x) ((coefficientMap N g).app n y) := by
  apply Module.ProductScalarKernel.element_ext (fun i => T'.obj (op ((N.obj (op n)).obj i)))
  intro i
  change BilinearPairing.projection N T' n i _ = BilinearPairing.projection N T' n i _
  rw [projection_coefficientMap, BilinearPairing.projection_pairing, BilinearPairing.projection_pairing,
    projection_coefficientMap, projection_coefficientMap]
  exact hc _ _ _

theorem cup_coefficient_natural
    (hc : ∀ U (x : P.obj U) (y : Q.obj U), h.app U (μ U x y) = ν U (f.app U x) (g.app U y))
    (p q : ℕ) (x : (BilinearPairing.cosimplicial N P).obj ⦋p⦌) (y : (BilinearPairing.cosimplicial N Q).obj ⦋q⦌) :
    (coefficientMap N h).app ⦋p + q⦌
        (Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N P) (BilinearPairing.cosimplicial N Q) (BilinearPairing.cosimplicial N T)
          (BilinearPairing.pairing N P Q T μ) p q x y) =
      Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N P') (BilinearPairing.cosimplicial N Q') (BilinearPairing.cosimplicial N T')
        (BilinearPairing.pairing N P' Q' T' ν) p q ((coefficientMap N f).app ⦋p⦌ x) ((coefficientMap N g).app ⦋q⦌ y) :=
  CosimplicialBilinearCup.cup_natural _ _ (coefficientMap N f) (coefficientMap N g)
    (coefficientMap N h) (pairing_coefficient_natural N μ ν f g h hc) p q x y

end Bilinear

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality
