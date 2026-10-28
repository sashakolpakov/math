import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry

/-! # Diagonal Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalQuotient.Tor

noncomputable section

/-! Native Tor of two quotient modules agrees with native Tor of the
diagonal quotient and the product quotient over the tensor algebra,
after restricting along the left tensor inclusion. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient
  ExternalQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I J : Ideal R)

def torIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (R ⊗[k] R))).obj
      (((Tor (ModuleCat (R ⊗[k] R)) n).obj
        (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ AlgebraDiagonalQuotient.diagonalIdeal k R))).obj
          (ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ ExternalQuotient.productIdeal k R R I J))) ≅
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R (R ⧸ J))) := by
  let A := R ⊗[k] R
  let D := ModuleCat.of A (A ⧸ AlgebraDiagonalQuotient.diagonalIdeal k R)
  let B := ModuleCat.of A (A ⧸ ExternalQuotient.productIdeal k R R I J)
  let G := ModuleCat.restrictScalars (algebraMap R A)
  exact G.mapIso (Symmetry.Tor.iso A D B n) ≪≫
    G.mapIso (((Tor (ModuleCat A) n).obj B).mapIso (AlgebraDiagonalQuotient.diagonalQuotientIso k R)) ≪≫
    G.mapIso (((Tor (ModuleCat A) n).mapIso (ExternalQuotient.productQuotientIso k R R I J).symm).app
      (DiagonalModule.diagonalModule k R)) ≪≫
    DiagonalComparison.Tor.torIso k R
      (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalQuotient.Tor
