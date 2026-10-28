import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange

/-! # Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Cup

noncomputable section

/-! The actual finite Čech coefficient isomorphism preserves the
Alexander–Whitney pairing with its literal sectionwise formula. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing

universe u v r s a b
variable {C : Type u} [Category.{v} C]
  {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  (F : ModuleCat.{a} R ⥤ ModuleCat.{b} S) [F.Additive]
  (η : ∀ M : ModuleCat.{a} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{a} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)

def component (P : Cᵒᵖ ⥤ ModuleCat.{a} R) (n : SimplexCategory) :
    (Cech.BilinearPairing.cosimplicial E P).obj n →+ (Cech.BilinearPairing.cosimplicial E (P ⋙ F)).obj n :=
  ((GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.cosimplicialIso F E hE P).hom.app n).hom.toAddMonoidHom.comp
    (η ((Cech.BilinearPairing.cosimplicial E P).obj n))

include hη in
theorem projection_component (P : Cᵒᵖ ⥤ ModuleCat.{a} R) (n : SimplexCategory)
    (i : (E.obj (op n)).I) (x : (Cech.BilinearPairing.cosimplicial E P).obj n) :
    Cech.BilinearPairing.projection E (P ⋙ F) n i (component F η E hE P n x) =
      η (P.obj (op ((E.obj (op n)).obj i))) (Cech.BilinearPairing.projection E P n i x) :=
  (ConcreteCategory.congr_hom (piComparison_comp_π F
    (fun j => P.obj (op ((E.obj (op n)).obj j))) i) (η _ x)).trans (hη _ x)

include hη in
theorem natural (P : Cᵒᵖ ⥤ ModuleCat.{a} R) {n m : SimplexCategory} (f : n ⟶ m)
    (x : (Cech.BilinearPairing.cosimplicial E P).obj n) :
    component F η E hE P m ((Cech.BilinearPairing.cosimplicial E P).map f x) =
      (Cech.BilinearPairing.cosimplicial E (P ⋙ F)).map f (component F η E hE P n x) :=
  (congrArg ((GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.cosimplicialIso F E hE P).hom.app m)
    (hη ((Cech.BilinearPairing.cosimplicial E P).map f) x).symm).trans
      (ConcreteCategory.congr_hom
        ((GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.cosimplicialIso F E hE P).hom.naturality f) (η _ x))

variable (P Q T : Cᵒᵖ ⥤ ModuleCat.{a} R)
  (μ : ∀ U, P.obj U →ₗ[R] Q.obj U →ₗ[R] T.obj U)
  (ν : ∀ U, F.obj (P.obj U) →ₗ[S] F.obj (Q.obj U) →ₗ[S] F.obj (T.obj U))
  (hprod : ∀ U (x : P.obj U) (y : Q.obj U),
    η (T.obj U) (μ U x y) = ν U (η (P.obj U) x) (η (Q.obj U) y))

include hη hprod in
theorem pairing (n : SimplexCategory) (x : (Cech.BilinearPairing.cosimplicial E P).obj n)
    (y : (Cech.BilinearPairing.cosimplicial E Q).obj n) :
    component F η E hE T n (Cech.BilinearPairing.pairing E P Q T μ n x y) =
      Cech.BilinearPairing.pairing E (P ⋙ F) (Q ⋙ F) (T ⋙ F) ν n
        (component F η E hE P n x) (component F η E hE Q n y) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => F.obj (T.obj (op ((E.obj (op n)).obj i))))
  intro i
  change Cech.BilinearPairing.projection E (T ⋙ F) n i _ = Cech.BilinearPairing.projection E (T ⋙ F) n i _
  rw [projection_component F η hη, Cech.BilinearPairing.projection_pairing, Cech.BilinearPairing.projection_pairing,
    projection_component F η hη, projection_component F η hη]
  exact hprod _ _ _

include hη hprod in
theorem cup (p q : ℕ) (x : (Cech.BilinearPairing.cosimplicial E P).obj ⦋p⦌)
    (y : (Cech.BilinearPairing.cosimplicial E Q).obj ⦋q⦌) :
    component F η E hE T ⦋p+q⦌
      (Cosimplicial.BilinearCup.cup (Cech.BilinearPairing.cosimplicial E P) (Cech.BilinearPairing.cosimplicial E Q)
        (Cech.BilinearPairing.cosimplicial E T) (Cech.BilinearPairing.pairing E P Q T μ) p q x y) =
      Cosimplicial.BilinearCup.cup (Cech.BilinearPairing.cosimplicial E (P ⋙ F)) (Cech.BilinearPairing.cosimplicial E (Q ⋙ F))
        (Cech.BilinearPairing.cosimplicial E (T ⋙ F)) (Cech.BilinearPairing.pairing E (P ⋙ F) (Q ⋙ F) (T ⋙ F) ν)
        p q (component F η E hE P ⦋p⦌ x) (component F η E hE Q ⦋q⦌ y) :=
  (pairing F η hη E hE P Q T μ ν hprod ⦋p+q⦌ _ _).trans
    (congrArg₂ (fun x y => Cech.BilinearPairing.pairing E (P ⋙ F) (Q ⋙ F) (T ⋙ F) ν ⦋p+q⦌ x y)
      (natural F η hη E hE P (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x)
      (natural F η hη E hE Q (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Cup
