import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice
import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation

/-! # Global Character Nontrivial -/

namespace OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial

noncomputable section

/-! Nontriviality of the archimedean character is derived from the global
arithmetic character, independently of any normalized local splitting. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]
variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

theorem archimedean_part_eq_one
    (hlocal : ∀ v : InfinitePlace F, ∀ t : v.Completion,
      Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t = 1)
    (a : InfiniteAdeleRing F) : ψ (a, 0) = 1 := by
  have he : (∑ v : InfinitePlace F, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) (a v)) = (a, 0) := by
    change (∑ v : InfinitePlace F, (Pi.single v (a v), (0 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))) = (a, 0)
    rw [← prod_mk_sum, Finset.sum_const_zero]
    congr 1
    funext v
    rw [Finset.sum_apply]
    exact Fintype.sum_pi_single v a
  rw [← he]
  have hs (s : Finset (InfinitePlace F)) : ψ (∑ v ∈ s, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) (a v)) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
      rw [Finset.sum_insert hv, ψ.map_add_eq_mul, ih,
        show ψ (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) (a v)) = 1 from hlocal v (a v), one_mul]
  exact hs Finset.univ

include hc hp in
theorem trivial_archimedean_implies_trivial
    (hlocal : ∀ v : InfinitePlace F, ∀ t : v.Completion,
      Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t = 1) : ∀ a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, ψ a = 1 := by
  have harch := archimedean_part_eq_one F ψ hlocal
  have hfinite (a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : ψ (0, a) = 1 := by
    apply (Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).induction_on
      (p := fun a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => ψ (0, a) = 1) a
      (isClosed_eq (hc.comp (continuous_const.prodMk continuous_id)) continuous_const)
    intro q
    have he : ((algebraMap F (InfiniteAdeleRing F) q, 0) : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) +
        (0, algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q := by
      apply Prod.ext
      · change algebraMap F (InfiniteAdeleRing F) q + 0 = _
        rw [add_zero]
        rfl
      · change 0 + algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q = _
        rw [zero_add]
        rfl
    have h := hp q
    rw [← he] at h
    erw [ψ.map_add_eq_mul, harch, one_mul] at h
    exact h
  intro a
  have he : ((a.1, 0) : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) + (0, a.2) = a := by
    apply Prod.ext
    · change a.1 + 0 = a.1
      exact add_zero _
    · change 0 + a.2 = a.2
      exact zero_add _
  rw [← he]
  erw [ψ.map_add_eq_mul, harch, hfinite, one_mul]

include hc hp in
theorem exists_archimedean_nontrivial (hn : ∃ a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, ψ a ≠ 1) :
    ∃ v : InfinitePlace F, ∃ t : v.Completion, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨a, ha⟩ := hn
  exact ha (trivial_archimedean_implies_trivial F ψ hc hp h a)

include hc hp in
theorem exists_nonzero_archimedean_linear_character
    (hu : ∀ a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, ‖ψ a‖ = 1) (hn : ∃ a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, ψ a ≠ 1) :
    ∃ L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      L ≠ 0 ∧ (∀ x, Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1 (L x)) ∧
        ∀ r : 𝓞 F, ∃ q : ℚ,
          (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)) := by
  obtain ⟨L, hL, hrat⟩ := Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.exists_archimedean_linear_character_rational F ψ hc hu hp
  refine ⟨L, ?_, hL, hrat⟩
  intro hzero
  obtain ⟨v, t, ht⟩ := exists_archimedean_nontrivial F ψ hc hp hn
  let a : InfiniteAdeleRing F := Pi.single v t
  have he : Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (InfiniteAdeleRing.ringEquiv_mixedSpace F a) = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) t := by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F a), 0) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  have h := hL (InfiniteAdeleRing.ringEquiv_mixedSpace F a)
  rw [hzero, LinearMap.zero_apply, (Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1).map_zero_eq_one] at h
  change ψ (Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (InfiniteAdeleRing.ringEquiv_mixedSpace F a)) = 1 at h
  rw [he] at h
  exact ht h

end

end OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial
