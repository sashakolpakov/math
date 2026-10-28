import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CosetPhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ProjectiveLevel

/-! # Projective Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProjectiveOpen.CM

noncomputable section

/-! Every concrete finite Schwartz test has an open projective
symplectic stabilizer. A finite coset expansion supplies all bounds;
no integral-support or smooth-action hypothesis is imposed. -/

open scoped Classical _root_.Matrix _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ProjectiveLevel.TestTransport

variable {I : Type*} [Fintype I] [DecidableEq I]

def CosetControl (N : ℕ) (hN : 0 < N) (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum g 0 a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne')) ∧
  CMExtraction.Finite.PhaseAction.TestTransport.finitePosition g 0 a - a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne') ∧
  (∑ i, CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum g 0 a i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (CMExtraction.Finite.PhaseAction.TestTransport.finitePosition g 0 a)) i) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele

theorem cosetControl_one (N : ℕ) (hN : 0 < N) (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    CosetControl N hN a 1 := by
  have hp : CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) 0 a = 0 := by
    unfold CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum
    rw [show (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf).val = 1 from rfl, Matrix.one_mulVec]
    rfl
  have hq : CMExtraction.Finite.PhaseAction.TestTransport.finitePosition (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) 0 a = a := by
    unfold CMExtraction.Finite.PhaseAction.TestTransport.finitePosition
    rw [show (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf).val = 1 from rfl, Matrix.one_mulVec]
    rfl
  simp only [CosetControl, hp, hq, sub_self, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  exact ⟨(RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice _ _).zero_mem, (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice _ _).zero_mem, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem⟩

theorem cosetControl_isOpen (N : ℕ) (hN : 0 < N) (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    IsOpen {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | CosetControl N hN a g} := by
  have hp : Continuous (fun g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum g 0 a) := by fun_prop
  have hq : Continuous (fun g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => CMExtraction.Finite.PhaseAction.TestTransport.finitePosition g 0 a - a) := by fun_prop
  have hc : Continuous (fun g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf =>
      ∑ i, CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum g 0 a i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (CMExtraction.Finite.PhaseAction.TestTransport.finitePosition g 0 a)) i) := by
    unfold RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale
    fun_prop
  exact ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen _ _).preimage hp).inter
    (((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen _ _).preimage hq).inter (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage hc))

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem controlled_cosets (N : ℕ) (hN : 0 < N) (m : MpF)
    (hm : CMExtraction.Finite.LatticeControl.TestTransport.FiniteLatticeControl N hN (D.finite.project m)) :
    ∃ c : ℂ, ∀ a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, CosetControl N hN a (D.finite.project m) →
      D.finite.action m (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (N : ℚ) (by exact_mod_cast hN.ne') a) =
        c • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (N : ℚ) (by exact_mod_cast hN.ne') a := by
  let r : ℚ := N
  have hr : r ≠ 0 := by
    change (N : ℚ) ≠ 0
    exact_mod_cast hN.ne'
  let f := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (ι := I) r hr
  obtain ⟨c, hc⟩ := CMExtraction.Finite.LatticeControl.TestTransport.finite_lattice_control_scalar D N hN m hm f
    (fun x hx => RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem r hr
      (fun h => hx (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral N hN h)))
    (fun u hu x => RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_add r hr hu x)
  refine ⟨c, ?_⟩
  intro a ha
  apply Subtype.ext
  funext x
  have ht := D.finite.intertwines m 0 a f (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a)
    (fun y => by rw [RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_heisenberg_translation]; rfl) x
  change (D.finite.action m (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a)).val x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter (CMExtraction.Finite.PhaseAction.TestTransport.finiteMomentum (D.finite.project m) 0 a)
      (CMExtraction.Finite.PhaseAction.TestTransport.finitePosition (D.finite.project m) 0 a) (D.finite.action m f).val x at ht
  rw [ht, hc]
  change _ * (c * f.val _) = c * (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a).val x
  rw [← mul_left_comm]
  exact congrArg (fun z : ℂ => c * z)
    (CosetPhase.CM.translate D r hr _ _ a ha.1 ha.2.1 ha.2.2 x)

theorem isOpen (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hφ : φ ≠ 0) :
    IsOpen (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ : Set (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  obtain ⟨N, hN, s, hs⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq φ
  let r : ℚ := N
  have hr : r ≠ 0 := by
    change (N : ℚ) ≠ 0
    exact_mod_cast hN.ne'
  let a := fun z : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := I) r hr => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep r hr z)
  let S := s.image a
  let W : Set (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := {g | CMExtraction.Finite.LatticeControl.TestTransport.FiniteLatticeControl N hN g ∧ ∀ b ∈ S, CosetControl N hN b g}
  have hw : IsOpen W := by
    have hi := isOpen_biInter_finset (s := S) (fun b _ => cosetControl_isOpen N hN b)
    have he : W = {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | CMExtraction.Finite.LatticeControl.TestTransport.FiniteLatticeControl N hN g} ∩
        (⋂ b ∈ S, {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | CosetControl N hN b g}) := by
      ext g
      simp [W]
    rw [he]
    exact (CMExtraction.Finite.ControlOpen.TestTransport.finiteLatticeControl_isOpen N hN).inter hi
  have h1 : (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ∈ W :=
    ⟨CMExtraction.Finite.ControlOpen.TestTransport.finiteLatticeControl_one N hN, fun b _ => cosetControl_one N hN b⟩
  apply (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset (hw.mem_nhds h1)
  intro g hg
  obtain ⟨m, rfl⟩ := D.finite.surjective g
  obtain ⟨c, hc⟩ := controlled_cosets D N hN m hg.1
  have he : D.finite.action m φ = c • φ := by
    rw [hs, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [map_smul, hc (a z) (hg.2 (a z) (Finset.mem_image_of_mem a hz)),
      smul_smul, smul_smul, mul_comm]
  exact (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer_mem D φ m).mpr
    ⟨Units.mk0 c (CMExtraction.EigenlineStabilizer.TestTransport.scalar_ne_zero_of_equiv D.finite.action φ m hφ c he), he⟩

def level (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hφ : φ ≠ 0) : OpenSubgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toSubgroup := CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ
  isOpen' := isOpen D φ hφ

theorem isOpen_all (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    IsOpen (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ : Set (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  by_cases hφ : φ = 0
  · subst φ
    have ht : (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D (0 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : Set (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro g
      obtain ⟨m, rfl⟩ := D.finite.surjective g
      exact (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer_mem D 0 m).mpr ⟨1, by simp⟩
    rw [ht]
    exact isOpen_univ
  · exact isOpen D φ hφ

def allLevel (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : OpenSubgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toSubgroup := CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ
  isOpen' := isOpen_all D φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProjectiveOpen.CM
