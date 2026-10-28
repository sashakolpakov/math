import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisNeighborhood

/-! # Differential Basis Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisLocalization.Neighborhood

noncomputable section

/-! The prescribed differential basis on any actual ring of sections
that is the principal determinant localization. -/

open _root_.Module
open scoped TensorProduct

universe u v w t
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {ι : Type w} [Fintype ι] [DecidableEq ι]
  (b : Basis ι A Ω[A⁄R]) (x : ι → A)
  (S : Type t) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
  [IsLocalization.Away (DifferentialBasisNeighborhood.determinant b x) S]

def differentialEquivAt : S ⊗[A] Ω[A⁄R] ≃ₗ[S] Ω[S⁄R] := by
  letI : Algebra.FormallyEtale A S :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (DifferentialBasisNeighborhood.determinant b x))
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S

def basisAt : Basis ι S Ω[S⁄R] :=
  (DeterminantBasisNeighborhood.basisOfIsUnitImage b
    (fun i => KaehlerDifferential.D R A (x i)) S
    (IsLocalization.Away.algebraMap_isUnit (DifferentialBasisNeighborhood.determinant b x))).map
      (differentialEquivAt b x S)

theorem basisAt_apply (i : ι) :
    basisAt b x S i = KaehlerDifferential.D R S (algebraMap A S (x i)) := by
  rw [basisAt, Basis.map_apply, DeterminantBasisNeighborhood.basisOfIsUnitImage_apply]
  change KaehlerDifferential.mapBaseChange R A S
    ((1 : S) ⊗ₜ[A] KaehlerDifferential.D R A (x i)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisLocalization.Neighborhood
