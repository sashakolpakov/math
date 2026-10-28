import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.ChosenProjectiveDepth
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ReferenceDepth
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepthTest

/-! # Joint Depth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepth.TestTransport

noncomputable section

/-! Combine the retained source level and same-test projective depth before choosing any finite prime. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ReferenceDepth.Approximation

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  {I : Type*} [Fintype I] [DecidableEq I]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (I ⊕ I → ℚ))
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
  (hfg : P.lattice.FG)
  (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
  (hφ : φ ≠ 0) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
  (N : ℕ) (hN : 0 < N)
  (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
    φ.val (u + x) = φ.val x)

theorem exists_retained_joint_depth (K₀ : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E P hP)) :
    ∃ M : ℕ, 0 < M ∧
      PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E P e D φ hfg hspan hφ hsupport N hN hperiod ∣ M ∧
      ∀ A : ℕ, M ∣ A → ∀ g : CM.FiniteAway.Approximation.CMFiniteSU E P hP,
        CM.AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP g ∈ P.adelicPrincipalLevel A → g ∈ K₀ := by
  exact JointDepthTest.Transport.exists_joint_depth (PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E P e D φ hfg hspan hφ hsupport N hN hperiod)
    (PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth_pos E P e D φ hfg hspan hφ hsupport N hN hperiod)
    (CM.ReferenceDepth.Approximation.cm_original_principal_depth E P hP K₀ hfg hspan)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepth.TestTransport
