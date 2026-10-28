import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Unramified Jacobian Criterion -/

namespace OAI.RepresentationTheory.Theta.Geometric.UnramifiedJacobianCriterion

noncomputable section

/-! For an unramified quotient of a smooth local presentation, a bound
on the number of cotangent relations forces the Jacobian to be invertible
on the residue field and hence gives formal smoothness. -/

open scoped TensorProduct
open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S)

theorem cotangentComplex_surjective_of_unramified [Algebra.FormallyUnramified R S] :
    Function.Surjective P.cotangentComplex := by
  intro x
  exact (P.exact_cotangentComplex_toKaehler x).mp (Subsingleton.elim _ _)

variable [IsLocalRing S] [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    [Algebra.FormallyUnramified R S]

include P in
theorem formallySmooth_of_unramified_cotangent_bound (hI : P.ker.FG)
    (hdim : Module.finrank (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) ≤
      Module.finrank (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace)) :
    Algebra.FormallySmooth R S := by
  have : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite hI
  let f := P.cotangentComplex.baseChange (IsLocalRing.ResidueField S)
  have hs : Function.Surjective f :=
    LinearMap.lTensor_surjective _ (cotangentComplex_surjective_of_unramified P)
  have heq : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.Cotangent) =
      Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] P.CotangentSpace) :=
    le_antisymm hdim (LinearMap.finrank_le_finrank_of_surjective hs)
  exact (Algebra.FormallySmooth.iff_injective_lTensor_residueField P hI).mpr
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hs)

end

end OAI.RepresentationTheory.Theta.Geometric.UnramifiedJacobianCriterion
