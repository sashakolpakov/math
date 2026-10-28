import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Cup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality

/-! # Morphism Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCup

noncomputable section

/-! A morphism after coefficient extension preserves the genuine
Čech cup when its section maps preserve products on original elements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality.Bilinear

universe u v r s a b
variable {C : Type u} [Category.{v} C]
  {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  (F : ModuleCat.{a} R ⥤ ModuleCat.{b} S) [F.Additive]
  (η : ∀ M : ModuleCat.{a} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{a} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)

def component {P : Cᵒᵖ ⥤ ModuleCat.{a} R} {P' : Cᵒᵖ ⥤ ModuleCat.{b} S}
    (f : P ⋙ F ⟶ P') (n : SimplexCategory) :
    (Cech.BilinearPairing.cosimplicial E P).obj n →+ (Cech.BilinearPairing.cosimplicial E P').obj n :=
  ((Cech.PairingNaturality.Bilinear.coefficientMap E f).app n).hom.toAddMonoidHom.comp
    (Cup.component F η E hE P n)

include hη in
theorem projection_component {P : Cᵒᵖ ⥤ ModuleCat.{a} R} {P' : Cᵒᵖ ⥤ ModuleCat.{b} S}
    (f : P ⋙ F ⟶ P') (n : SimplexCategory) (i : (E.obj (op n)).I)
    (x : (Cech.BilinearPairing.cosimplicial E P).obj n) :
    Cech.BilinearPairing.projection E P' n i (component F η E hE f n x) =
      f.app (op ((E.obj (op n)).obj i))
        (η (P.obj (op ((E.obj (op n)).obj i))) (Cech.BilinearPairing.projection E P n i x)) := by
  change Cech.BilinearPairing.projection E P' n i
    ((Cech.PairingNaturality.Bilinear.coefficientMap E f).app n (Cup.component F η E hE P n x)) = _
  rw [Cech.PairingNaturality.Bilinear.projection_coefficientMap, Cup.projection_component F η hη]

include hη in
theorem natural {P : Cᵒᵖ ⥤ ModuleCat.{a} R} {P' : Cᵒᵖ ⥤ ModuleCat.{b} S}
    (f : P ⋙ F ⟶ P') {n m : SimplexCategory} (t : n ⟶ m)
    (x : (Cech.BilinearPairing.cosimplicial E P).obj n) :
    component F η E hE f m ((Cech.BilinearPairing.cosimplicial E P).map t x) =
      (Cech.BilinearPairing.cosimplicial E P').map t (component F η E hE f n x) := by
  change (Cech.PairingNaturality.Bilinear.coefficientMap E f).app m
    (Cup.component F η E hE P m ((Cech.BilinearPairing.cosimplicial E P).map t x)) = _
  rw [Cup.natural F η hη]
  exact ConcreteCategory.congr_hom ((Cech.PairingNaturality.Bilinear.coefficientMap E f).naturality t)
    (Cup.component F η E hE P n x)

variable (P Q T : Cᵒᵖ ⥤ ModuleCat.{a} R) (P' Q' T' : Cᵒᵖ ⥤ ModuleCat.{b} S)
  (f : P ⋙ F ⟶ P') (g : Q ⋙ F ⟶ Q') (h : T ⋙ F ⟶ T')
  (μ : ∀ U, P.obj U →ₗ[R] Q.obj U →ₗ[R] T.obj U)
  (ν : ∀ U, P'.obj U →ₗ[S] Q'.obj U →ₗ[S] T'.obj U)
  (hprod : ∀ U (x : P.obj U) (y : Q.obj U),
    h.app U (η (T.obj U) (μ U x y)) =
      ν U (f.app U (η (P.obj U) x)) (g.app U (η (Q.obj U) y)))

include hη hprod in
theorem pairing (n : SimplexCategory) (x : (Cech.BilinearPairing.cosimplicial E P).obj n)
    (y : (Cech.BilinearPairing.cosimplicial E Q).obj n) :
    component F η E hE h n (Cech.BilinearPairing.pairing E P Q T μ n x y) =
      Cech.BilinearPairing.pairing E P' Q' T' ν n
        (component F η E hE f n x) (component F η E hE g n y) := by
  apply Module.ProductScalarKernel.element_ext (fun i => T'.obj (op ((E.obj (op n)).obj i)))
  intro i
  change Cech.BilinearPairing.projection E T' n i _ = Cech.BilinearPairing.projection E T' n i _
  rw [projection_component F η hη, Cech.BilinearPairing.projection_pairing, Cech.BilinearPairing.projection_pairing,
    projection_component F η hη, projection_component F η hη]
  exact hprod _ _ _

include hη hprod in
theorem cup (p q : ℕ) (x : (Cech.BilinearPairing.cosimplicial E P).obj ⦋p⦌)
    (y : (Cech.BilinearPairing.cosimplicial E Q).obj ⦋q⦌) :
    component F η E hE h ⦋p+q⦌
      (Cosimplicial.BilinearCup.cup (Cech.BilinearPairing.cosimplicial E P) (Cech.BilinearPairing.cosimplicial E Q)
        (Cech.BilinearPairing.cosimplicial E T) (Cech.BilinearPairing.pairing E P Q T μ) p q x y) =
      Cosimplicial.BilinearCup.cup (Cech.BilinearPairing.cosimplicial E P') (Cech.BilinearPairing.cosimplicial E Q')
        (Cech.BilinearPairing.cosimplicial E T') (Cech.BilinearPairing.pairing E P' Q' T' ν) p q
        (component F η E hE f ⦋p⦌ x) (component F η E hE g ⦋q⦌ y) :=
  (pairing F η hη E hE P Q T P' Q' T' f g h μ ν hprod ⦋p+q⦌ _ _).trans
    (congrArg₂ (fun x y => Cech.BilinearPairing.pairing E P' Q' T' ν ⦋p+q⦌ x y)
      (natural F η hη E hE f (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x)
      (natural F η hη E hE g (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCup
