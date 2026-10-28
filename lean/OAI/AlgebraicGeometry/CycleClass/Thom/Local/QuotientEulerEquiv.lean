import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatLength
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Quotient Euler Equiv -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions

noncomputable section

/-! The exact native Tor Euler sum for two quotient modules is
invariant under local ring isomorphisms, including its infinite-length
and truncation conventions. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatLength.Tor
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem euler_quotients_congr (R : Type u) [CommRing R] (I J I' J' : Ideal R)
    (hI : I = I') (hJ : J = J') (d : ℕ) :
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) d =
      TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ I')) (ModuleCat.of R (R ⧸ J')) d := by
  cases hI
  cases hJ
  rfl

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def quotientBaseChangeIso (I : Ideal R) :
    (TorAlgebra.FlatExtension.baseChange R S).obj (ModuleCat.of R (R ⧸ I)) ≅ ModuleCat.of S (S ⧸ I.map (algebraMap R S)) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso

theorem euler_quotients_baseChange [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (I J : Ideal R) (d : ℕ)
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) d =
      TorAlgebra.Euler.Tor.euler S (ModuleCat.of S (S ⧸ I.map (algebraMap R S)))
        (ModuleCat.of S (S ⧸ J.map (algebraMap R S))) d := by
  have he := TorAlgebra.FlatLength.Tor.euler_length_of_maximalIdeal R S (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) d h
  change TorAlgebra.Euler.Tor.euler S ((TorAlgebra.FlatExtension.baseChange R S).obj (ModuleCat.of R (R ⧸ I)))
    ((TorAlgebra.FlatExtension.baseChange R S).obj (ModuleCat.of R (R ⧸ J))) d = _ at he
  exact he.symm.trans ((TorAlgebra.IsolatedEuler.euler_iso_left S (quotientBaseChangeIso R S I) _ d).trans
    (TorAlgebra.EulerTransport.Tor.iso_right S _ (quotientBaseChangeIso R S J) d))

omit [Algebra R S] in
theorem euler_quotients_ringEquiv [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (I J : Ideal R) (d : ℕ) :
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) d =
      TorAlgebra.Euler.Tor.euler S (ModuleCat.of S (S ⧸ I.map e.toRingHom)) (ModuleCat.of S (S ⧸ J.map e.toRingHom)) d := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let ea : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  let : Module.Flat R S := Module.Flat.of_linearEquiv ea.toLinearEquiv.symm
  let : IsLocalHom (algebraMap R S) := ⟨fun b hb =>
    (congrArg IsUnit (e.symm_apply_apply b)).mp (hb.map e.symm.toMonoidHom)⟩
  apply euler_quotients_baseChange R S I J d
  rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]
  exact Ideal.map_comap_of_surjective _ e.surjective _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions
