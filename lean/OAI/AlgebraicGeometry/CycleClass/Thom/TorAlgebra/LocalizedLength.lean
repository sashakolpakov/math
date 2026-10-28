import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Localized Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalizedLength.Tor

noncomputable section

/-! The length of a localized native Tor module equals the length
of native Tor over the local ring. For quotient inputs, the modules
are exactly the quotients by the localized ideals. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

universe u
variable (R : Type u) [CommRing R] (p : PrimeSpectrum R)

def localizedTorIso (M N : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (((Tor (ModuleCat R) n).obj M).obj N)) ≅
    (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
      ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)).obj
        ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj N)) :=
  (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl
    (((Tor (ModuleCat R) n).obj M).obj N)).toModuleIso ≪≫
    (FlatExtension.torBaseChangeIso R (Localization.AtPrime p.asIdeal) M N n).symm

def localizedQuotientIso (I : Ideal R) :
    (FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime p.asIdeal) I).symm.toLinearEquiv.toModuleIso

def quotientTorIso (I J : Ideal R) (n : ℕ) :
    ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (((Tor (ModuleCat R) n).obj
        (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R (R ⧸ J)))) ≅
    (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
      (ModuleCat.of (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))))).obj
      (ModuleCat.of (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⧸ J.map (algebraMap R (Localization.AtPrime p.asIdeal))))) :=
  localizedTorIso R p (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) n ≪≫
  (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).mapIso (localizedQuotientIso R p I)).app _) ≪≫
  ((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj _).mapIso (localizedQuotientIso R p J)

theorem quotientTor_length (I J : Ideal R) (n : ℕ) :
    LocalizedModuleLength.Constructions.localLength R (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
      (ModuleCat.of R (R ⧸ J))) p =
    Module.length (Localization.AtPrime p.asIdeal)
      (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          ((Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))))).obj
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          ((Localization.AtPrime p.asIdeal) ⧸ J.map (algebraMap R (Localization.AtPrime p.asIdeal))))) :=
  (quotientTorIso R p I J n).toLinearEquiv.length_eq

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalizedLength.Tor
