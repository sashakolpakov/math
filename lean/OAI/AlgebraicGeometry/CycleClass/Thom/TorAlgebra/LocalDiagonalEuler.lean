import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalLength
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalizedLength

/-! # Local Diagonal Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler

noncomputable section

/-! Local reduction to the diagonal compares native Tor over the
local tensor algebra and over the original local ring, with the actual
localized diagonal and product ideals and identical truncation bounds. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

def diagonalPrime (q : PrimeSpectrum R) : PrimeSpectrum (R ⊗[k] R) :=
  PrimeSpectrum.comap (Algebra.TensorProduct.lmul' k).toRingHom q

def localizedQuotient (B : Type u) [CommRing B] (p : PrimeSpectrum B) (I : Ideal B) :
    ModuleCat.{u} (Localization.AtPrime p.asIdeal) :=
  ModuleCat.of (Localization.AtPrime p.asIdeal)
    ((Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap B (Localization.AtPrime p.asIdeal)))

theorem tor_length (q : PrimeSpectrum R) (I J : Ideal R) (n : ℕ) :
    Module.length (Localization.AtPrime (diagonalPrime k R q).asIdeal)
      (((Tor (ModuleCat (Localization.AtPrime (diagonalPrime k R q).asIdeal)) n).obj
        (localizedQuotient (R ⊗[k] R) (diagonalPrime k R q) (AlgebraDiagonalQuotient.diagonalIdeal k R))).obj
          (localizedQuotient (R ⊗[k] R) (diagonalPrime k R q) (ExternalQuotient.productIdeal k R R I J))) =
    Module.length (Localization.AtPrime q.asIdeal)
      (((Tor (ModuleCat (Localization.AtPrime q.asIdeal)) n).obj
        (localizedQuotient R q I)).obj (localizedQuotient R q J)) :=
  (LocalizedLength.Tor.quotientTor_length (R ⊗[k] R) (diagonalPrime k R q)
    (AlgebraDiagonalQuotient.diagonalIdeal k R) (ExternalQuotient.productIdeal k R R I J) n).symm.trans
      ((DiagonalLength.Tor.tor_localLength k R I J q n).trans
        (LocalizedLength.Tor.quotientTor_length R q I J n))

theorem euler_eq (q : PrimeSpectrum R) (I J : Ideal R) (d : ℕ) :
    Euler.Tor.euler (Localization.AtPrime (diagonalPrime k R q).asIdeal)
      (localizedQuotient (R ⊗[k] R) (diagonalPrime k R q) (AlgebraDiagonalQuotient.diagonalIdeal k R))
      (localizedQuotient (R ⊗[k] R) (diagonalPrime k R q) (ExternalQuotient.productIdeal k R R I J)) d =
    Euler.Tor.euler (Localization.AtPrime q.asIdeal) (localizedQuotient R q I) (localizedQuotient R q J) d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ)) (tor_length k R q I J n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler
