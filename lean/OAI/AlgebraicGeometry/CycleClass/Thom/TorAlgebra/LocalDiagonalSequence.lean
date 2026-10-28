import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler

/-! # Local Diagonal Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalSequence

noncomputable section

/-! In unramified polynomial coordinates the native local
intersection Euler characteristic is the Euler characteristic against
the actual quotient by the diagonal coordinate sequence. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient
  ExternalQuotient Euler.Tor
  Local.PolynomialDiagonalIdeal.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) k) R] [IsScalarTower k (MvPolynomial (Fin n) k) R]
  [Algebra.FormallyUnramified (MvPolynomial (Fin n) k) R]
  [IsNoetherianRing (R ⊗[MvPolynomial (Fin n) k] R)]

def sequenceQuotientIso (q : PrimeSpectrum R) :
    ModuleCat.of (Localization.AtPrime (LocalDiagonalEuler.diagonalPrime k R q).asIdeal)
      ((Localization.AtPrime (LocalDiagonalEuler.diagonalPrime k R q).asIdeal) ⧸ Ideal.ofList (Local.PolynomialDiagonalIdeal.Constructions.localEquations k R n q)) ≅
      LocalDiagonalEuler.localizedQuotient (R ⊗[k] R) (LocalDiagonalEuler.diagonalPrime k R q) (AlgebraDiagonalQuotient.diagonalIdeal k R) :=
  (Ideal.quotientEquivAlgOfEq
    (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))
    (Local.PolynomialDiagonalIdeal.Constructions.ideal_ofList_localEquations k R n q)).toLinearEquiv.toModuleIso

theorem euler_eq_sequence (q : PrimeSpectrum R) (I J : Ideal R) (d : ℕ) :
    Euler.Tor.euler (Localization.AtPrime q.asIdeal) (LocalDiagonalEuler.localizedQuotient R q I) (LocalDiagonalEuler.localizedQuotient R q J) d =
    Euler.Tor.euler (Localization.AtPrime (LocalDiagonalEuler.diagonalPrime k R q).asIdeal)
      (ModuleCat.of (Localization.AtPrime (LocalDiagonalEuler.diagonalPrime k R q).asIdeal)
        ((Localization.AtPrime (LocalDiagonalEuler.diagonalPrime k R q).asIdeal) ⧸ Ideal.ofList (Local.PolynomialDiagonalIdeal.Constructions.localEquations k R n q)))
      (LocalDiagonalEuler.localizedQuotient (R ⊗[k] R) (LocalDiagonalEuler.diagonalPrime k R q) (ExternalQuotient.productIdeal k R R I J)) d :=
  (LocalDiagonalEuler.euler_eq k R q I J d).symm.trans
    (IsolatedEuler.euler_iso_left _ (sequenceQuotientIso k R n q).symm _ d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalSequence
