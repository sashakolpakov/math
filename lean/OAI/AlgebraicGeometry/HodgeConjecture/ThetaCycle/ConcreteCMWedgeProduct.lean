import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteWedgeDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CommonPrincipalWedges

/-! # Concrete CM Wedge Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteCMWedgeProduct.CM

noncomputable section

/-! The actual fixed total theta input yields a nonzero CM wedge product.
Full native ThetaKernel supplies the finite decompositions, full PairingContinuity selects the
nonzero approximation, and full HeckeCycles controls all factors on a common cover. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.Data

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D) (hid : ∀ i, (v i).val 1 = true)

include T hid in
theorem exists_actual_principal_cm_wedge_product
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement) (hPairingContinuity : Persistence.CM.PairingContinuityInput.{0, 0, 0}) (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput) :
    ∃ (M : ℕ) (hM : 0 < M) (hDM : D.depth ∣ M),
      CommonPrincipalWedges.CM.HasCMWedgeProduct K (v := v) (D.surface M hM hDM).surface := by
  obtain ⟨N, hN, hDN, forms, hforms, _, hpersist⟩ :=
    ConcretePrincipalPersistence.CM.exists_actual_principal_theta_persistence K D T hid hPairingContinuity
  obtain ⟨n, α, β, hα, hβ, _, _, _, hn⟩ := hpersist
  obtain ⟨c₀, r, φ₀, ψ₀, hfirst⟩ := ConcreteWedgeDecomposition.CM.actual_initial_theta_wedge_decomposition K D T hid hAdelicTheta
  obtain ⟨c₁, s, φ₁, ψ₁, hsecond⟩ := ConcreteWedgeDecomposition.CM.actual_approximation_theta_wedge_decomposition K D T hid
    hAdelicTheta n (forms n) (hforms n).1 (hforms n).2.2
  exact CommonPrincipalWedges.CM.common_principal_wedge_product K D (ApproximationSequence.CM.approximationSequence K D n) hid hHeckeCycles
    N hN hDN α β r s φ₀ ψ₀ φ₁ ψ₁ c₀ c₁ (hα.trans hfirst) (hβ.trans hsecond) hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteCMWedgeProduct.CM
