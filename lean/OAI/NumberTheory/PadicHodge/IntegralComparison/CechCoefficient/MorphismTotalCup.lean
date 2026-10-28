import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality

/-! # Morphism Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismTotalCup

noncomputable section

/-! A genuine coefficient-change morphism preserves the signed cup
on the original finite Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality

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
  (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{b} S) ℕ)
  (f : GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P ⟶ Q)

def cochainMap : (F.mapHomologicalComplex (.up ℕ)).obj (Presheaf.TotalCup.CechProduct.total E P) ⟶ Presheaf.TotalCup.CechProduct.total E Q :=
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom ≫ Presheaf.CechProductNaturality.totalMap E f

def map (n : ℕ) : (Presheaf.TotalCup.CechProduct.total E P).X n →+ (Presheaf.TotalCup.CechProduct.total E Q).X n :=
  ((cochainMap F E hE P Q f).f n).hom.toAddMonoidHom.comp (η ((Presheaf.TotalCup.CechProduct.total E P).X n))

def row (p q : ℕ) := MorphismCup.component F η E hE (f.f p) ⦋q⦌

include hη in
theorem injection (p q n : ℕ) (h : p+q=n) (x : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X p).X q) :
    MorphismTotalCup.map F η E hE P Q f n ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p q n h x) =
      (Presheaf.TotalCup.CechProduct.bicomplex E Q).ιTotal (.up ℕ) p q n h (row F η E hE P Q f p q x) := by
  change (Presheaf.CechProductNaturality.totalMap E f).f n
    (TotalCup.map F η E hE P n
      ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p q n h x)) = _
  rw [TotalCup.injection F η hη]
  exact ConcreteCategory.congr_hom
    ((Presheaf.TotalCup.CechProduct.bicomplex E (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P)).ιTotal_map
      (Presheaf.TotalCup.CechProduct.bicomplex E Q) (Presheaf.CechProductNaturality.bicomplexMap E f) (.up ℕ) p q n h)
    (TotalCup.row F η E hE P p q x)

variable
  (μ : ∀ p q U, (P.X p).obj U →ₗ[R] (P.X q).obj U →ₗ[R] (P.X (p+q)).obj U)
  (ν : ∀ p q U, (Q.X p).obj U →ₗ[S] (Q.X q).obj U →ₗ[S] (Q.X (p+q)).obj U)
  (hprod : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    (f.f (p+q)).app U (η ((P.X (p+q)).obj U) (μ p q U x y)) =
      ν p q U ((f.f p).app U (η ((P.X p).obj U) x))
        ((f.f q).app U (η ((P.X q).obj U) y)))

include hη hprod in
theorem row_cup (p q j k : ℕ) (x : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X p).X j)
    (y : ((Presheaf.TotalCup.CechProduct.bicomplex E P).X q).X k) :
    row F η E hE P Q f (p+q) (j+k) (Presheaf.CechProduct.cup E P μ p q j k x y) =
      Presheaf.CechProduct.cup E Q ν p q j k (row F η E hE P Q f p j x) (row F η E hE P Q f q k y) :=
  MorphismCup.cup F η hη E hE
    (P.X p) (P.X q) (P.X (p+q)) (Q.X p) (Q.X q) (Q.X (p+q))
    (f.f p) (f.f q) (f.f (p+q)) (μ p q) (ν p q) (hprod p q) j k x y

include hη hprod in
theorem map_cup (n m : ℕ) (x : (Presheaf.TotalCup.CechProduct.total E P).X n) (y : (Presheaf.TotalCup.CechProduct.total E P).X m) :
    MorphismTotalCup.map F η E hE P Q f (n+m) (Presheaf.TotalCup.CechProduct.totalCup E P μ n m x y) =
      Presheaf.TotalCup.CechProduct.totalCup E Q ν n m (MorphismTotalCup.map F η E hE P Q f n x) (MorphismTotalCup.map F η E hE P Q f m y) := by
  let A := (LinearMap.toAddMonoidHom'.comp (Presheaf.TotalCup.CechProduct.totalCup E P μ n m).toAddMonoidHom).compr₂
    (MorphismTotalCup.map F η E hE P Q f (n+m))
  let B := ((LinearMap.toAddMonoidHom'.comp (Presheaf.TotalCup.CechProduct.totalCup E Q ν n m).toAddMonoidHom).compl₂
    (MorphismTotalCup.map F η E hE P Q f m)).comp (MorphismTotalCup.map F η E hE P Q f n)
  have hab : A = B := by
    apply TotalBiadditiveExt.biadditive_ext (Presheaf.TotalCup.CechProduct.bicomplex E P) (Presheaf.TotalCup.CechProduct.bicomplex E P) n m
    intro p j q k hpj hqk u v
    change MorphismTotalCup.map F η E hE P Q f (n+m)
        (Presheaf.TotalCup.CechProduct.totalCup E P μ n m ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p j n hpj u)
          ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) q k m hqk v)) =
      Presheaf.TotalCup.CechProduct.totalCup E Q ν n m (MorphismTotalCup.map F η E hE P Q f n ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) p j n hpj u))
        (MorphismTotalCup.map F η E hE P Q f m ((Presheaf.TotalCup.CechProduct.bicomplex E P).ιTotal (.up ℕ) q k m hqk v))
    have hi := injection F η hη E hE P Q f (p+q) (j+k) (n+m) (by omega)
      (Presheaf.CechProduct.cup E P μ p q j k u v)
    have hc := congrArg ((Presheaf.TotalCup.CechProduct.bicomplex E Q).ιTotal (.up ℕ) (p+q) (j+k) (n+m) (by change (p+q)+(j+k)=n+m; omega))
      (row_cup F η hη E hE P Q f μ ν hprod p q j k u v)
    exact (congrArg (MorphismTotalCup.map F η E hE P Q f (n+m)) (Presheaf.TotalCup.CechProduct.totalCup_ι E P μ n m p j q k hpj hqk u v)).trans
      ((map_zsmul (MorphismTotalCup.map F η E hE P Q f (n+m)) ((-1 : ℤ)^(j*q)) _).trans
        ((congrArg ((-1 : ℤ)^(j*q) • ·) (hi.trans hc)).trans
          ((Presheaf.TotalCup.CechProduct.totalCup_ι E Q ν n m p j q k hpj hqk (row F η E hE P Q f p j u)
            (row F η E hE P Q f q k v)).symm.trans
              (congrArg₂ (fun x y => Presheaf.TotalCup.CechProduct.totalCup E Q ν n m x y)
                (injection F η hη E hE P Q f p j n hpj u).symm
                (injection F η hη E hE P Q f q k m hqk v).symm))))
  exact DFunLike.congr_fun (DFunLike.congr_fun hab x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.MorphismTotalCup
