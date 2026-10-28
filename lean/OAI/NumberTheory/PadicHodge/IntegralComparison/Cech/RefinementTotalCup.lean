import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Refinement Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementTotalCup

noncomputable section

/-! Literal Čech cover refinement preserves the signed total cup and
its induced product on categorical cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct.Cech

universe u v a r
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {R : Type r} [CommRing R] {ι κ : Type}
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{a} R) ℕ)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

def bicomplexMap : Presheaf.TotalCup.CechProduct.bicomplex N P ⟶ Presheaf.TotalCup.CechProduct.bicomplex N' P where
  f q := GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (P.X q)
  comm' q q' _ := (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.naturality U V r (P.d q q')).symm

def map : Presheaf.TotalCup.CechProduct.total N P ⟶ Presheaf.TotalCup.CechProduct.total N' P :=
  HomologicalComplex₂.total.map (bicomplexMap U V r P) (.up ℕ)

variable (μ : ∀ p q W, (P.X p).obj W →ₗ[R] (P.X q).obj W →ₗ[R] (P.X (p+q)).obj W)
  (hμ : ∀ p q {W Z : Cᵒᵖ} (f : W ⟶ Z) (x : (P.X p).obj W) (y : (P.X q).obj W),
    (P.X (p+q)).map f (μ p q W x y) = μ p q Z ((P.X p).map f x) ((P.X q).map f y))

include hμ in
theorem bicomplex_pairing (p i q j : ℕ)
    (x : ((Presheaf.TotalCup.CechProduct.bicomplex N P).X p).X i) (y : ((Presheaf.TotalCup.CechProduct.bicomplex N P).X q).X j) :
    (((bicomplexMap U V r P).f (p+q)).f (i+j))
      (Presheaf.TotalCup.CechProduct.signedPairing N P μ p i q j x y) =
    Presheaf.TotalCup.CechProduct.signedPairing N' P μ p i q j
      (((bicomplexMap U V r P).f p).f i x) (((bicomplexMap U V r P).f q).f j y) := by
  change (((bicomplexMap U V r P).f (p+q)).f (i+j))
    ((-1 : ℤ)^(i*q) • Presheaf.CechProduct.cup N P μ p q i j x y) =
      (-1 : ℤ)^(i*q) • Presheaf.CechProduct.cup N' P μ p q i j
        (((bicomplexMap U V r P).f p).f i x) (((bicomplexMap U V r P).f q).f j y)
  exact (map_zsmul (((bicomplexMap U V r P).f (p+q)).f (i+j)).hom
    ((-1 : ℤ)^(i*q)) _).trans
      (congrArg ((-1 : ℤ)^(i*q) • ·)
        (RefinementCup.cup_map U V r (P.X p) (P.X q) (P.X (p+q))
          (μ p q) (hμ p q) i j x y))

include hμ in
theorem map_cup (i j : ℕ) (x : (Presheaf.TotalCup.CechProduct.total N P).X i) (y : (Presheaf.TotalCup.CechProduct.total N P).X j) :
    (RefinementTotalCup.map U V r P).f (i+j) (Presheaf.TotalCup.CechProduct.totalCup N P μ i j x y) =
      Presheaf.TotalCup.CechProduct.totalCup N' P μ i j ((RefinementTotalCup.map U V r P).f i x) ((RefinementTotalCup.map U V r P).f j y) :=
  BicomplexPairingNaturality.totalPairing_natural (Presheaf.TotalCup.CechProduct.signedPairing N P μ) (Presheaf.TotalCup.CechProduct.signedPairing N' P μ)
    (bicomplexMap U V r P) (bicomplexMap U V r P) (bicomplexMap U V r P)
    (bicomplex_pairing U V r P μ hμ) i j x y

variable (dμ : ∀ p q W (x : (P.X p).obj W) (y : (P.X q).obj W),
    (P.d (p+q) (p+q+1)).app W (μ p q W x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (p+1)+q=p+q+1) W
        (μ (p+1) q W ((P.d p (p+1)).app W x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast P (by omega : p+(q+1)=p+q+1) W
        (μ p (q+1) W x ((P.d q (q+1)).app W y)))

abbrev homologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (Presheaf.TotalCup.CechProduct.totalCup N P μ) (Presheaf.TotalCup.CechProduct.totalCup N' P μ)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N P μ hμ dμ) (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N' P μ hμ dμ)
  (RefinementTotalCup.map U V r P) (map_cup U V r P μ hμ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementTotalCup
