import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Annihilator
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler
import OAI.AlgebraicGeometry.CycleClass.Thom.RetractLocalLength

/-! # Diagonal Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalLength.Tor

noncomputable section

/-! Reduction to the diagonal preserves the exact lengths of native
Tor modules, globally and after localization at corresponding primes.
The proof uses the diagonal ideal's actual annihilation of Tor. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient
  Euler.Tor LocalizedModuleLength.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I J : Ideal R)

abbrev torModule (n : ℕ) : ModuleCat.{u} (R ⊗[k] R) :=
  (((Tor (ModuleCat (R ⊗[k] R)) n).obj
    (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ AlgebraDiagonalQuotient.diagonalIdeal k R))).obj
      (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ ExternalQuotient.productIdeal k R R I J)))

theorem diagonal_le_annihilator (n : ℕ) :
    AlgebraDiagonalQuotient.diagonalIdeal k R ≤ Module.annihilator (R ⊗[k] R) (torModule k R I J n) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  apply Annihilator.Tor.first
  apply Module.mem_annihilator.mp
  rwa [Ideal.annihilator_quotient]

theorem tor_length (n : ℕ) :
    Module.length (R ⊗[k] R) (torModule k R I J n) =
      Module.length R (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
        (ModuleCat.of R (R ⧸ J))) :=
  (RetractModuleLength.Constructions.length_eq R (R ⊗[k] R) (Algebra.TensorProduct.lmul'' k)
    (torModule k R I J n) (diagonal_le_annihilator k R I J n)).trans
      (DiagonalQuotient.Tor.torIso k R I J n).toLinearEquiv.length_eq

theorem tor_localLength (q : PrimeSpectrum R) (n : ℕ) :
    LocalizedModuleLength.Constructions.localLength (R ⊗[k] R) (torModule k R I J n)
      (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' k).toRingHom q) =
    LocalizedModuleLength.Constructions.localLength R (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj
      (ModuleCat.of R (R ⧸ J))) q :=
  (RetractLocalLength.Constructions.localLength_eq R (R ⊗[k] R) (Algebra.TensorProduct.lmul'' k)
    (torModule k R I J n) (diagonal_le_annihilator k R I J n) q).trans
      (LocalizedModuleLength.Constructions.localLength_equiv (DiagonalQuotient.Tor.torIso k R I J n).toLinearEquiv q)

theorem euler_eq (d : ℕ) :
    Euler.Tor.euler (R ⊗[k] R)
      (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ AlgebraDiagonalQuotient.diagonalIdeal k R))
      (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ ExternalQuotient.productIdeal k R R I J)) d =
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ)) (tor_length k R I J n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalLength.Tor
