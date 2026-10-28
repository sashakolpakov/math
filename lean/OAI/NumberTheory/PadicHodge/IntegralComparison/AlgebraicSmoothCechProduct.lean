import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothPresheafProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairingNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalCup

/-! # Algebraic Smooth Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCechProduct

noncomputable section

/-! The original algebraic-to-smooth comparison preserves the
signed products on the actual Čech total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

def smoothCochains (p : ℕ) : CosimplicialObject (ModuleCat.{0} ℂ) :=
  Cech.BilinearPairing.cosimplicial N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p)

def pairing (p q : ℕ) (n : SimplexCategory) :
    (smoothCochains X N p).obj n →ₗ[ℂ] (smoothCochains X N q).obj n →ₗ[ℂ]
      (smoothCochains X N (p + q)).obj n :=
  Cech.BilinearPairing.pairing N _ _ _ (AlgebraicSmoothPresheafProduct.pairing X p q) n

def cup (p q a b : ℕ) :
    (smoothCochains X N p).obj ⦋a⦌ →ₗ[ℂ] (smoothCochains X N q).obj ⦋b⦌ →ₗ[ℂ]
      (smoothCochains X N (p + q)).obj ⦋a + b⦌ :=
  Cosimplicial.BilinearCup.cup _ _ _ (pairing X N p q) a b

def smoothBicomplex : HomologicalComplex₂ (ModuleCat.{0} ℂ) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex N (AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X)

def signedPairing (p a q b : ℕ) :
    ((smoothBicomplex X N).X p).X a →ₗ[ℂ] ((smoothBicomplex X N).X q).X b →ₗ[ℂ]
      ((smoothBicomplex X N).X (p + q)).X (a + b) :=
  (-1 : ℤ) ^ (a * q) • cup X N p q a b

def smoothTotal : CochainComplex (ModuleCat.{0} ℂ) ℕ := (smoothBicomplex X N).total (.up ℕ)

def totalPairing (n m : ℕ) : (smoothTotal X N).X n →ₗ[ℂ] (smoothTotal X N).X m →ₗ[ℂ]
    (smoothTotal X N).X (n + m) :=
  BicomplexPairing.totalPairing _ _ _ (signedPairing X N) n m

def bicomplexMap : RationalDeRham.TotalCup.Cech.bicomplex ℂ X N ⟶ smoothBicomplex X N :=
  ((FormalCoproduct.cochainComplexFunctor N).mapHomologicalComplex (.up ℕ)).map
    (AlgebraicSmoothPresheafProduct.nativeMap X)

def totalMap : RationalDeRham.TotalCup.Cech.total ℂ X N ⟶ smoothTotal X N :=
  HomologicalComplex₂.total.map (bicomplexMap X N) (.up ℕ)

theorem bicomplexMap_pairing (p a q b : ℕ)
    (x : ((RationalDeRham.TotalCup.Cech.bicomplex ℂ X N).X p).X a)
    (y : ((RationalDeRham.TotalCup.Cech.bicomplex ℂ X N).X q).X b) :
    ((bicomplexMap X N).f (p + q)).f (a + b)
        (RationalDeRham.TotalCup.Cech.signedPairing ℂ X N p a q b x y) =
      signedPairing X N p a q b (((bicomplexMap X N).f p).f a x) (((bicomplexMap X N).f q).f b y) := by
  have h := Cech.PairingNaturality.Bilinear.cup_coefficient_natural N
    (RationalDeRham.CechCup.sectionPairing ℂ X p q)
    (AlgebraicSmoothPresheafProduct.pairing X p q)
    ((AlgebraicSmoothPresheafProduct.nativeMap X).f p)
    ((AlgebraicSmoothPresheafProduct.nativeMap X).f q)
    ((AlgebraicSmoothPresheafProduct.nativeMap X).f (p + q))
    (AlgebraicSmoothPresheafProduct.nativeMap_pairing X p q) a b x y
  change ((bicomplexMap X N).f (p + q)).f (a + b)
    ((-1 : ℤ) ^ (a * q) • RationalDeRham.CechCup.cup ℂ X N p q a b x y) =
      (-1 : ℤ) ^ (a * q) • cup X N p q a b
        (((bicomplexMap X N).f p).f a x) (((bicomplexMap X N).f q).f b y)
  exact (map_zsmul (((bicomplexMap X N).f (p + q)).f (a + b)).hom ((-1 : ℤ) ^ (a * q))
    (RationalDeRham.CechCup.cup ℂ X N p q a b x y)).trans
    (congrArg ((-1 : ℤ) ^ (a * q) • ·) h)

theorem totalMap_pairing (n m : ℕ)
    (x : (RationalDeRham.TotalCup.Cech.total ℂ X N).X n)
    (y : (RationalDeRham.TotalCup.Cech.total ℂ X N).X m) :
    (totalMap X N).f (n + m) (RationalDeRham.TotalCup.Cech.totalCup ℂ X N n m x y) =
      totalPairing X N n m ((totalMap X N).f n x) ((totalMap X N).f m y) :=
  BicomplexPairingNaturality.totalPairing_natural
    (RationalDeRham.TotalCup.Cech.signedPairing ℂ X N) (signedPairing X N)
    (bicomplexMap X N) (bicomplexMap X N) (bicomplexMap X N) (bicomplexMap_pairing X N) n m x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCechProduct
