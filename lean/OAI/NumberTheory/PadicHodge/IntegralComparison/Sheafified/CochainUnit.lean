import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Cochain Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainUnit.Pairing

noncomputable section

/-! The literal sheafification unit is a product-preserving map of
the original cochain complexes and their native Čech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (w)) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

def unit : P ⟶ CochainPairing.complex J R P where
  f a := (sheafificationAdjunction J (ModuleCat.{w} R)).unit.app (P.X a)
  comm' a b _ := ((sheafificationAdjunction J (ModuleCat.{w} R)).unit.naturality (P.d a b)).symm

variable (μ : ∀ a b (V : Cᵒᵖ), (P.X a).obj V →ₗ[R]
  (P.X b).obj V →ₗ[R] (P.X (a + b)).obj V)
  (hμ : ∀ a b {V W : Cᵒᵖ} (f : V ⟶ W) x y,
    (P.X (a + b)).map f (μ a b V x y) = μ a b W ((P.X a).map f x) ((P.X b).map f y))

theorem unit_pairing (a b : ℕ) (V : Cᵒᵖ) (x : (P.X a).obj V) (y : (P.X b).obj V) :
    ((Pairing.unit.{u, v, w} J R P).f (a + b)).app V (μ a b V x y) =
      CochainPairing.pairing J R P μ hμ a b V (((Pairing.unit.{u, v, w} J R P).f a).app V x) (((Pairing.unit.{u, v, w} J R P).f b).app V y) :=
  BilinearPairing.unit_pairing R (P.X a) (P.X b) (P.X (a + b))
    (μ a b) (hμ a b) J V x y

theorem pairing_natural (a b : ℕ) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : ((CochainPairing.complex J R P).X a).obj V) (y : ((CochainPairing.complex J R P).X b).obj V) :
    ((CochainPairing.complex J R P).X (a + b)).map f (CochainPairing.pairing J R P μ hμ a b V x y) =
      CochainPairing.pairing J R P μ hμ a b W (((CochainPairing.complex J R P).X a).map f x) (((CochainPairing.complex J R P).X b).map f y) :=
  BilinearPairing.pairing_natural R (P.X a) (P.X b) (P.X (a + b))
    (μ a b) (hμ a b) J f x y

end

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max z w)) [CommRing R] [HasSheafify J (ModuleCat.{max z w} R)]
  [(J.W (A := ModuleCat.{max z w} R)).IsMonoidal]
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max z w} R) ℕ)

variable (μ : ∀ a b (V : Cᵒᵖ), (P.X a).obj V →ₗ[R]
  (P.X b).obj V →ₗ[R] (P.X (a + b)).obj V)
  (hμ : ∀ a b {V W : Cᵒᵖ} (f : V ⟶ W) x y,
    (P.X (a + b)).map f (μ a b V x y) = μ a b W ((P.X a).map f x) ((P.X b).map f y))

variable (dμ : ∀ a b (V : Cᵒᵖ) x y,
  (P.d (a + b) (a + b + 1)).app V (μ a b V x y) =
    Presheaf.CechProduct.sectionDegreeCast P (by omega : (a + 1) + b = a + b + 1) V
      (μ (a + 1) b V ((P.d a (a + 1)).app V x) y) +
    (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast P
      (by omega : a + (b + 1) = a + b + 1) V
      (μ a (b + 1) V x ((P.d b (b + 1)).app V y)))
  (N : SimplicialObject (FormalCoproduct.{z} C))

include dμ in
theorem unit_cohomologyCup (a b : ℕ)
    (x : (Presheaf.TotalCup.CechProduct.total N P).homology a)
    (y : (Presheaf.TotalCup.CechProduct.total N P).homology b) :
    HomologicalComplex.homologyMap (Presheaf.CechProductNaturality.totalMap N (Pairing.unit.{u, v, max z w} J R P)) (a + b)
      (Presheaf.CohomologyProduct.Cech.cohomologyCup N P μ hμ dμ a b x y) =
    Presheaf.CohomologyProduct.Cech.cohomologyCup N (CochainPairing.complex J R P) (CochainPairing.pairing J R P μ hμ)
      (pairing_natural.{u, v, max z w} J R P μ hμ) (CochainPairing.differential J R P μ hμ dμ) a b
      (HomologicalComplex.homologyMap (Presheaf.CechProductNaturality.totalMap N (Pairing.unit.{u, v, max z w} J R P)) a x)
      (HomologicalComplex.homologyMap (Presheaf.CechProductNaturality.totalMap N (Pairing.unit.{u, v, max z w} J R P)) b y) :=
  Presheaf.CohomologyProduct.Cech.totalMap_cohomologyCup N P μ hμ dμ
    (CochainPairing.complex J R P) (CochainPairing.pairing J R P μ hμ) (pairing_natural.{u, v, max z w} J R P μ hμ)
    (CochainPairing.differential J R P μ hμ dμ) (Pairing.unit.{u, v, max z w} J R P) (unit_pairing.{u, v, max z w} J R P μ hμ) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainUnit.Pairing
