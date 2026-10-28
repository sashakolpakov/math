import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ProductBaseChangeCup
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Base Change Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeTotalCup.Product

noncomputable section

/-! The original intersection-coordinate isomorphism preserves the
signed product on Čech totals and their categorical cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct.Cech

universe u v s t r a
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {R : Type r} [CommRing R]
  (F : C ⥤ D) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  (P : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{a} R) ℕ)

def pulled := ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{a} R) F).mapHomologicalComplex
  (.up ℕ)).obj P

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeTotalCup.Product.pulled F P
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (Functor.obj F ∘ U)

def map : Presheaf.TotalCup.CechProduct.total N Q ⟶ Presheaf.TotalCup.CechProduct.total N' P :=
  HomologicalComplex₂.total.map (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom (.up ℕ)

variable
  (μ : ∀ p q V, (P.X p).obj V →ₗ[R] (P.X q).obj V →ₗ[R] (P.X (p+q)).obj V)
  (hμ : ∀ p q {V W : Dᵒᵖ} (f : V ⟶ W) (x : (P.X p).obj V) (y : (P.X q).obj V),
    (P.X (p+q)).map f (μ p q V x y) = μ p q W ((P.X p).map f x) ((P.X q).map f y))

def pairing (p q : ℕ) (V : Cᵒᵖ) :
    ((Q).X p).obj V →ₗ[R] ((Q).X q).obj V →ₗ[R] ((Q).X (p+q)).obj V := μ p q (F.op.obj V)

include hμ in
omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
theorem pairing_natural (p q : ℕ) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : ((Q).X p).obj V) (y : ((Q).X q).obj V) :
    ((Q).X (p+q)).map f (pairing F P μ p q V x y) =
      pairing F P μ p q W (((Q).X p).map f x) (((Q).X q).map f y) := hμ p q (F.op.map f) x y

include hμ in
theorem bicomplex_pairing (p i q j : ℕ)
    (x : ((Presheaf.TotalCup.CechProduct.bicomplex N Q).X p).X i) (y : ((Presheaf.TotalCup.CechProduct.bicomplex N Q).X q).X j) :
    (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom.f (p+q)).f (i+j))
        (Presheaf.TotalCup.CechProduct.signedPairing N Q (pairing F P μ) p i q j x y) =
      Presheaf.TotalCup.CechProduct.signedPairing N' P μ p i q j
        (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom.f p).f i x)
        (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom.f q).f j y) := by
  change (ProductBaseChangeCup.map F U (P.X (p+q))).app ⦋i+j⦌
      ((-1 : ℤ)^(i*q) • Presheaf.CechProduct.cup N Q (pairing F P μ) p q i j x y) =
    (-1 : ℤ)^(i*q) • Presheaf.CechProduct.cup N' P μ p q i j
      ((ProductBaseChangeCup.map F U (P.X p)).app ⦋i⦌ x)
      ((ProductBaseChangeCup.map F U (P.X q)).app ⦋j⦌ y)
  exact (map_zsmul ((ProductBaseChangeCup.map F U (P.X (p+q))).app ⦋i+j⦌).hom
    ((-1 : ℤ)^(i*q)) _).trans
      (congrArg ((-1 : ℤ)^(i*q) • ·)
        (ProductBaseChangeCup.cup_natural F U (P.X p) (P.X q) (P.X (p+q))
          (μ p q) (hμ p q) i j x y))

include hμ in
theorem map_cup (i j : ℕ) (x : (Presheaf.TotalCup.CechProduct.total N Q).X i) (y : (Presheaf.TotalCup.CechProduct.total N Q).X j) :
    (Product.map F U P).f (i+j) (Presheaf.TotalCup.CechProduct.totalCup N Q (pairing F P μ) i j x y) =
      Presheaf.TotalCup.CechProduct.totalCup N' P μ i j ((Product.map F U P).f i x) ((Product.map F U P).f j y) :=
  BicomplexPairingNaturality.totalPairing_natural (Presheaf.TotalCup.CechProduct.signedPairing N Q (pairing F P μ))
    (Presheaf.TotalCup.CechProduct.signedPairing N' P μ) (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom
    (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P).hom
    (bicomplex_pairing F U P μ hμ) i j x y

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
private theorem cast_eq {i j : ℕ} (h : i=j) (V : Cᵒᵖ) (x : (P.X i).obj (F.op.obj V)) :
    Presheaf.CechProduct.sectionDegreeCast Q h V x = Presheaf.CechProduct.sectionDegreeCast P h (F.op.obj V) x := by subst j; rfl

variable (dμ : ∀ p q V (x : (P.X p).obj V) (y : (P.X q).obj V),
    (P.d (p+q) (p+q+1)).app V (μ p q V x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (p+1)+q=p+q+1) V (μ (p+1) q V ((P.d p (p+1)).app V x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast P (by omega : p+(q+1)=p+q+1) V
        (μ p (q+1) V x ((P.d q (q+1)).app V y)))

include dμ in
omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
theorem differential (p q : ℕ) (V : Cᵒᵖ)
    (x : ((Q).X p).obj V) (y : ((Q).X q).obj V) :
    ((Q).d (p+q) (p+q+1)).app V (pairing F P μ p q V x y) =
      Presheaf.CechProduct.sectionDegreeCast Q (by omega : (p+1)+q=p+q+1) V
        (pairing F P μ (p+1) q V (((Q).d p (p+1)).app V x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast Q (by omega : p+(q+1)=p+q+1) V
        (pairing F P μ p (q+1) V x (((Q).d q (q+1)).app V y)) := by
  exact (dμ p q (F.op.obj V) x y).trans
    (congrArg₂ (fun x y : (P.X (p+q+1)).obj (F.op.obj V) => x + (-1 : ℤ)^p • y)
      (cast_eq F P (by omega : (p+1)+q=p+q+1) V _).symm
      (cast_eq F P (by omega : p+(q+1)=p+q+1) V _).symm)

abbrev cohomologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (Presheaf.TotalCup.CechProduct.totalCup N Q (pairing F P μ)) (Presheaf.TotalCup.CechProduct.totalCup N' P μ)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N Q (pairing F P μ) (pairing_natural F P μ hμ) (differential F P μ dμ))
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N' P μ hμ dμ) (Product.map F U P) (map_cup F U P μ hμ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeTotalCup.Product
