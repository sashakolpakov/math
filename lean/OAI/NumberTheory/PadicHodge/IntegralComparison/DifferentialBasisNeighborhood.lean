import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantBasisNeighborhood
import Mathlib.RingTheory.Etale.Kaehler

/-! # Differential Basis Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisNeighborhood

noncomputable section

/-! Prescribed exact differentials form the literal Kähler basis on their
principal determinant neighborhood. A quotient basis ensures that this
neighborhood contains the entire quotient. -/

open _root_.Module
open scoped TensorProduct

universe u v w t
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {ι : Type w} [Fintype ι] [DecidableEq ι]
  (b : Basis ι A Ω[A⁄R]) (x : ι → A)

abbrev determinant : A := b.det (fun i => KaehlerDifferential.D R A (x i))

abbrev Ring := Localization.Away (determinant b x)

def differentialEquiv :
    Ring b x ⊗[A] Ω[A⁄R] ≃ₗ[Ring b x] Ω[Ring b x⁄R] := by
  letI : Algebra.FormallyEtale A (Ring b x) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (determinant b x))
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A (Ring b x)

def basis : Basis ι (Ring b x) Ω[Ring b x⁄R] :=
  (DeterminantBasisNeighborhood.localizedBasis b
    (fun i => KaehlerDifferential.D R A (x i))).map (differentialEquiv b x)

theorem basis_apply (i : ι) :
    basis b x i = KaehlerDifferential.D R (Ring b x) (algebraMap A (Ring b x) (x i)) := by
  rw [basis, Basis.map_apply, DeterminantBasisNeighborhood.localizedBasis_apply]
  change KaehlerDifferential.mapBaseChange R A (Ring b x)
    ((1 : Ring b x) ⊗ₜ[A] KaehlerDifferential.D R A (x i)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

variable (Q : Type t) [CommRing Q] [Algebra A Q]

theorem image_isUnit (c : Basis ι Q (Q ⊗[A] Ω[A⁄R]))
    (hc : ∀ i, c i = (1 : Q) ⊗ₜ[A] KaehlerDifferential.D R A (x i)) :
    IsUnit (algebraMap A Q (determinant b x)) :=
  DeterminantBasisNeighborhood.image_isUnit b
    (fun i => KaehlerDifferential.D R A (x i)) Q c hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisNeighborhood
