import OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial

/-! # Finite Character Annihilator -/

namespace OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterAnnihilator

noncomputable section

/-! The integral annihilator of the finite character, constructed directly
from the global additive character before any local splitting is chosen. -/

open scoped _root_.NumberField Classical _root_.Topology
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

def finiteCharacter (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ℂ :=
  ψ.compAddMonoidHom
    { toFun := fun a => (0, a)
      map_zero' := rfl
      map_add' := fun a b => by
        change ((0 : InfiniteAdeleRing F), a + b) = (0 + 0, a + b)
        rw [add_zero] }

theorem finiteCharacter_continuous (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) :
    Continuous (finiteCharacter F ψ) :=
  hc.comp (continuous_const.prodMk continuous_id)

def integralAnnihilator (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) : AddSubgroup (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) where
  carrier := {a | ∀ b : Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F, finiteCharacter F ψ (a * b.val) = 1}
  zero_mem' := by intro b; simp
  add_mem' := by
    intro a c ha hc b
    rw [add_mul, (finiteCharacter F ψ).map_add_eq_mul, ha b, hc b, one_mul]
  neg_mem' := by
    intro a ha b
    rw [neg_mul, (finiteCharacter F ψ).map_neg_eq_inv, ha b, inv_one]

theorem integralAnnihilator_isClosed
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) :
    IsClosed (integralAnnihilator F ψ : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) := by
  change IsClosed {a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F | ∀ b : Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F,
    finiteCharacter F ψ (a * b.val) = 1}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun b => isClosed_eq
    ((finiteCharacter_continuous F ψ hc).comp (continuous_id.mul continuous_const)) continuous_const)

theorem integralAnnihilator_contains_multiple
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F,
      (M : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) * b.val ∈ integralAnnihilator F ψ := by
  obtain ⟨M, hM, h⟩ := Weil.AdelicSplitting.FiniteCharacterConductor.Construction.exists_finite_character_conductor F ψ hc hu
  refine ⟨M, hM, fun b c => ?_⟩
  change ψ (0, ((M : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) * b.val) * c.val) = 1
  rw [mul_assoc]
  exact h (b * c)

theorem integralAnnihilator_isOpen
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) :
    IsOpen (integralAnnihilator F ψ : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) := by
  obtain ⟨M, hM, h⟩ := integralAnnihilator_contains_multiple F ψ hc hu
  have hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  let U : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    {a | algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((M : F)⁻¹) * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F}
  have hU : IsOpen U := (Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage
    (continuous_const.mul continuous_id)
  have hz : (0 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ∈ U := by
    change _ * 0 ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F
    rw [mul_zero]
    exact zero_mem _
  apply (integralAnnihilator F ψ).isOpen_of_mem_nhds
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro a ha
  have hh := h ⟨algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((M : F)⁻¹) * a, ha⟩
  have he : (M : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) *
      (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((M : F)⁻¹) * a) = a := by
    rw [← map_natCast (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) M, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hMF, map_one, one_mul]
  exact he ▸ hh

theorem rational_character_pair
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) (q : F) :
    Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (mixedEmbedding F q) *
      finiteCharacter F ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = 1 := by
  change ψ (Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (mixedEmbedding F q)) *
    ψ (0, algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = 1
  rw [Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_rational]
  erw [← ψ.map_add_eq_mul]
  have he : ((algebraMap F (InfiniteAdeleRing F) q, 0) : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) +
      (0, algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q := by
    apply Prod.ext
    · change algebraMap F (InfiniteAdeleRing F) q + 0 = _
      rw [add_zero]
      rfl
    · change 0 + algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q = _
      rw [zero_add]
      rfl
  erw [he, hp]

theorem rational_mem_integralAnnihilator_iff
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x, Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1 (L x)) (a : F) :
    algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a ∈ integralAnnihilator F ψ ↔
      ∀ r : 𝓞 F, ∃ z : ℤ, (z : ℝ) =
        L (mixedEmbedding F (a * algebraMap (𝓞 F) F r)) := by
  constructor
  · intro ha r
    have hf := ha (Weil.AdelicSplitting.IntegralAdeles.Construction.integerToFiniteIntegral F r)
    change finiteCharacter F ψ
      (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a * algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r) = 1 at hf
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F), ← map_mul] at hf
    have h := rational_character_pair F ψ hp (a * algebraMap (𝓞 F) F r)
    rw [hf, mul_one, hL] at h
    exact (Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff _).mp h
  · intro ha b
    apply (Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_integer_finiteIntegralRing F).induction_on
      (p := fun b : Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F =>
        finiteCharacter F ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a * b.val) = 1) b
      (isClosed_eq ((finiteCharacter_continuous F ψ hc).comp
        (continuous_const.mul continuous_subtype_val)) continuous_const)
    intro r
    have h := rational_character_pair F ψ hp (a * algebraMap (𝓞 F) F r)
    have harch : Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ
        (mixedEmbedding F (a * algebraMap (𝓞 F) F r)) = 1 := by
      rw [hL]
      exact (Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff _).mpr (ha r)
    rw [harch, one_mul] at h
    change finiteCharacter F ψ
      (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a * algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F), ← map_mul]
    exact h

end

end OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterAnnihilator
