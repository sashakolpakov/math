import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatLength
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Base Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.QuotientBaseChange

noncomputable section

/-! Flat local base change of native Tor for actual quotient modules.
When the maximal ideal extends to the maximal ideal, every Tor length
is unchanged. This includes the stalk isomorphisms of open components. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

namespace Tor

universe u

theorem residue_quotient_length (R : Type u) [CommRing R] [IsLocalRing R] :
    Module.length R (R ⧸ IsLocalRing.maximalIdeal R) = 1 := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  rw [Module.length_eq_of_surjective (M := R ⧸ IsLocalRing.maximalIdeal R)
    (show Function.Surjective (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) from
      Ideal.Quotient.mk_surjective)]
  exact Module.length_eq_one (R ⧸ IsLocalRing.maximalIdeal R) (R ⧸ IsLocalRing.maximalIdeal R)

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

def torIso (I J : Ideal R) (n : ℕ) :
    (((Tor (ModuleCat S) n).obj (.of S (S ⧸ I.map (algebraMap R S)))).obj
      (.of S (S ⧸ J.map (algebraMap R S)))) ≅
    (((Tor (ModuleCat S) n).obj ((FlatExtension.baseChange R S).obj (.of R (R ⧸ I)))).obj
      ((FlatExtension.baseChange R S).obj (.of R (R ⧸ J)))) := by
  let eI := (Ideal.qoutMapEquivTensorQout (R := R) (I := I) S).toModuleIso
  let eJ := (Ideal.qoutMapEquivTensorQout (R := R) (I := J) S).toModuleIso
  exact (((Tor (ModuleCat S) n).mapIso eI).app (.of S (S ⧸ J.map (algebraMap R S)))) ≪≫
    (((Tor (ModuleCat S) n).obj ((FlatExtension.baseChange R S).obj (.of R (R ⧸ I)))).mapIso eJ)

theorem length_eq (I J : Ideal R) (n : ℕ)
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    Module.length S (((Tor (ModuleCat S) n).obj (.of S (S ⧸ I.map (algebraMap R S)))).obj
      (.of S (S ⧸ J.map (algebraMap R S)))) =
    Module.length R (((Tor (ModuleCat R) n).obj (.of R (R ⧸ I))).obj (.of R (R ⧸ J))) := by
  rw [(torIso R S I J n).toLinearEquiv.length_eq, FlatLength.Tor.tor_length, hmax,
    residue_quotient_length, mul_one]

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.QuotientBaseChange
