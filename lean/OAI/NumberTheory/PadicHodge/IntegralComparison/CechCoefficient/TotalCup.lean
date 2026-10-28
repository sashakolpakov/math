import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Cup
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalBiadditiveExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup

/-! # Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCup

noncomputable section

/-! Exact coefficient change preserves the signed product on the
original finite Čech total, including both totalization signs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup.CechProduct

universe u v r s a b
variable {C : Type u} [Category.{v} C]
  {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  (F : ModuleCat.{a} R ⥤ ModuleCat.{b} S) [F.Additive]
  (η : ∀ M : ModuleCat.{a} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{a} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{a} R) ℕ)

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P

def map (n : ℕ) : (Presheaf.TotalCup.CechProduct.total E P).X n →+ (Presheaf.TotalCup.CechProduct.total E Q).X n :=
  ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom.f n).hom.toAddMonoidHom.comp
    (η ((Presheaf.TotalCup.CechProduct.total E P).X n))

def row (p q : ℕ) := Cup.component F η E hE (P.X p) ⦋q⦌

theorem row_eq (p q : ℕ) (x : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X p).X q) :
    ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom.f p).f q
      (η _ x) = row F η E hE P p q x :=
  ConcreteCategory.congr_hom (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f F E hE (P.X p) q) (η _ x)

include hη in
theorem injection (p q n : ℕ) (h : p+q=n) (x : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X p).X q) :
    TotalCup.map F η E hE P n ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p q n h x) =
      (Presheaf.TotalCup.CechProduct.bicomplex E Q).ιTotal (.up ℕ) p q n h (row F η E hE P p q x) :=
  (congrArg ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom.f n)
    (hη ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p q n h) x).symm).trans
      ((ConcreteCategory.congr_hom
        (TotalCoordinates.injection F E hE P p q n h) (η _ x)).trans
          (congrArg ((Presheaf.TotalCup.CechProduct.bicomplex E Q).ιTotal (.up ℕ) p q n h) (row_eq F η E hE P p q x)))

variable
  (μ : ∀ p q U, (P.X p).obj U →ₗ[R] (P.X q).obj U →ₗ[R] (P.X (p+q)).obj U)
  (ν : ∀ p q U, F.obj ((P.X p).obj U) →ₗ[S] F.obj ((P.X q).obj U) →ₗ[S]
    F.obj ((P.X (p+q)).obj U))
  (hprod : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    η ((P.X (p+q)).obj U) (μ p q U x y) =
      ν p q U (η ((P.X p).obj U) x) (η ((P.X q).obj U) y))

include hη hprod in
theorem row_cup (p q j k : ℕ) (x : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X p).X j)
    (y : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X q).X k) :
    row F η E hE P (p+q) (j+k) (Presheaf.CechProduct.cup E P μ p q j k x y) =
      Presheaf.CechProduct.cup E Q ν p q j k (row F η E hE P p j x) (row F η E hE P q k y) :=
  Cup.cup F η hη E hE (P.X p) (P.X q) (P.X (p+q))
    (μ p q) (ν p q) (hprod p q) j k x y

include hη hprod in
theorem map_cup (n m : ℕ) (x : (Presheaf.TotalCup.CechProduct.total E P).X n) (y : (Presheaf.TotalCup.CechProduct.total E P).X m) :
    TotalCup.map F η E hE P (n+m) (Presheaf.TotalCup.CechProduct.totalCup E P μ n m x y) =
      Presheaf.TotalCup.CechProduct.totalCup E Q ν n m (TotalCup.map F η E hE P n x) (TotalCup.map F η E hE P m y) := by
  let A := (LinearMap.toAddMonoidHom'.comp (Presheaf.TotalCup.CechProduct.totalCup E P μ n m).toAddMonoidHom).compr₂
    (TotalCup.map F η E hE P (n+m))
  let B := ((LinearMap.toAddMonoidHom'.comp (Presheaf.TotalCup.CechProduct.totalCup E Q ν n m).toAddMonoidHom).compl₂
    (TotalCup.map F η E hE P m)).comp (TotalCup.map F η E hE P n)
  have hab : A = B := by
    apply TotalBiadditiveExt.biadditive_ext (Presheaf.TotalCup.CechProduct.bicomplex E P) (Presheaf.TotalCup.CechProduct.bicomplex E P) n m
    intro p j q k hpj hqk u v
    change TotalCup.map F η E hE P (n+m)
        (Presheaf.TotalCup.CechProduct.totalCup E P μ n m ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p j n hpj u)
          ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) q k m hqk v)) =
      Presheaf.TotalCup.CechProduct.totalCup E Q ν n m (TotalCup.map F η E hE P n ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p j n hpj u))
        (TotalCup.map F η E hE P m ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) q k m hqk v))
    have hi := injection F η hη E hE P (p+q) (j+k) (n+m) (by omega)
      (Presheaf.CechProduct.cup E P μ p q j k u v)
    have hc := congrArg ((Presheaf.TotalCup.CechProduct.bicomplex E Q).ιTotal (.up ℕ) (p+q) (j+k) (n+m) (by change (p+q)+(j+k)=n+m; omega))
      (row_cup F η hη E hE P μ ν hprod p q j k u v)
    exact (congrArg (TotalCup.map F η E hE P (n+m)) (Presheaf.TotalCup.CechProduct.totalCup_ι E P μ n m p j q k hpj hqk u v)).trans
      ((map_zsmul (TotalCup.map F η E hE P (n+m)) ((-1 : ℤ)^(j*q)) _).trans
        ((congrArg ((-1 : ℤ)^(j*q) • ·) (hi.trans hc)).trans
          ((Presheaf.TotalCup.CechProduct.totalCup_ι E Q ν n m p j q k hpj hqk (row F η E hE P p j u)
            (row F η E hE P q k v)).symm.trans
              (congrArg₂ (fun x y => Presheaf.TotalCup.CechProduct.totalCup E Q ν n m x y)
                (injection F η hη E hE P p j n hpj u).symm
                (injection F η hη E hE P q k m hqk v).symm))))
  exact DFunLike.congr_fun (DFunLike.congr_fun hab x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCup
