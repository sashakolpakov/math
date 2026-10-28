import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.NeighborhoodDepth
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ProjectiveLevel

/-! # Chosen Projective Depth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.ChosenProjectiveDepth.TestTransport

noncomputable section

section

/-! A principal depth in the original PEL group is chosen before any
finite prime, using the retained rational phase basis and the same test. -/

open scoped Classical _root_.Matrix _root_.Topology

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.NeighborhoodDepth.Approximation

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  {I : Type*} [Fintype I] [DecidableEq I]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (I ⊕ I → ℚ))
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)

theorem pel_projective_principal_depth
    (hfg : P.lattice.FG)
    (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (hφ : φ ≠ 0) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (u + x) = φ.val x) :
    ∃ M : ℕ, 0 < M ∧ ∀ A : ℕ, M ∣ A →
      ∀ g ∈ P.adelicPrincipalLevel A, ∀ m : MpF,
        (D.finite.project m).val = PhaseCoordinates.TestTransport.pelPhaseMatrix E P e g →
          ∃ c : ℂˣ, D.finite.action m φ = (c : ℂ) • φ := by
  have hcontrol := (Finite.ControlOpen.TestTransport.finiteLatticeControl_isOpen (I := I) N hN).mem_nhds
    (Finite.ControlOpen.TestTransport.finiteLatticeControl_one N hN)
  rw [nhds_subtype_eq_comap] at hcontrol
  change {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | Finite.LatticeControl.TestTransport.FiniteLatticeControl N hN g} ∈
    Filter.comap Subtype.val (𝓝 (1 : Matrix (I ⊕ I) (I ⊕ I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) at hcontrol
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hcontrol
  have hpre : (PhaseCoordinates.TestTransport.pelPhaseMatrix E P e) ⁻¹' U ∈ 𝓝 (1 : P.FiniteSpecialUnitary) :=
    (PhaseCoordinates.TestTransport.pelPhaseMatrix_continuous E P e).continuousAt.preimage_mem_nhds
      ((PhaseCoordinates.TestTransport.pelPhaseMatrix_one E P e).symm ▸ hU)
  obtain ⟨M, hM, hdepth⟩ := NeighborhoodDepth.Approximation.pel_principal_neighborhood_depth P hfg hspan _ hpre
  refine ⟨M, hM, ?_⟩
  intro A hA g hg m hm
  have hmc : Finite.LatticeControl.TestTransport.FiniteLatticeControl N hN (D.finite.project m) := by
    apply hsub
    change (D.finite.project m).val ∈ U
    rw [hm]
    exact hdepth A hA hg
  obtain ⟨c, hc⟩ := Finite.LatticeControl.TestTransport.finite_lattice_control_scalar D N hN m hmc φ hsupport hperiod
  exact ⟨Units.mk0 c (EigenlineStabilizer.TestTransport.scalar_ne_zero_of_equiv D.finite.action φ m hφ c hc), hc⟩

end

/-! Retain one original PEL principal depth for the same finite test.
Its definition has no finite prime or local coordinate lift as input. -/

open scoped Classical _root_.Matrix

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
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

def pelProjectiveDepth : ℕ :=
  (pel_projective_principal_depth E P e D φ hfg hspan hφ hsupport N hN hperiod).choose

theorem pelProjectiveDepth_pos : 0 < pelProjectiveDepth E P e D φ hfg hspan hφ hsupport N hN hperiod :=
  (pel_projective_principal_depth E P e D φ hfg hspan hφ hsupport N hN hperiod).choose_spec.1

theorem pelProjectiveDepth_scalar (A : ℕ)
    (hA : pelProjectiveDepth E P e D φ hfg hspan hφ hsupport N hN hperiod ∣ A)
    (g : P.FiniteSpecialUnitary) (hg : g ∈ P.adelicPrincipalLevel A)
    (m : MpF) (hm : (D.finite.project m).val = PhaseCoordinates.TestTransport.pelPhaseMatrix E P e g) :
    ∃ c : ℂˣ, D.finite.action m φ = (c : ℂ) • φ :=
  (pel_projective_principal_depth E P e D φ hfg hspan hφ hsupport N hN hperiod).choose_spec.2 A hA g hg m hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.ChosenProjectiveDepth.TestTransport
