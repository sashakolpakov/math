import OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing

/-! # Archimedean Nontrivial -/

namespace OAI.RepresentationTheory.Theta.Adelic.ArchimedeanNontrivial

noncomputable section

/-! Every archimedean component of the actual nontrivial principal-trivial
adelic character is nontrivial. This precedes local splitting construction. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing

theorem realCharacter_half_ne_one : Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1 (1 / 2) ≠ 1 := by
  rw [Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter_apply]
  have he : (((2 * Real.pi * 1 * (1 / 2) : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]
  norm_num

theorem archimedean_character_nontrivial
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (v : InfinitePlace F) :
    ∃ t : v.Completion, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1 := by
  obtain ⟨L, hL0, hL, hrat⟩ := GlobalCharacterNontrivial.exists_nonzero_archimedean_linear_character F ψ hc hp hu hn
  have hsep := RationalCharacterPairing.linear_pairing_nondegenerate F L hL0 hrat
  by_contra hlocal
  simp only [not_exists, not_not] at hlocal
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let x := e (Pi.single v 1)
  have hchar (y : mixedEmbedding.mixedSpace F) : Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1 (L (x * y)) = 1 := by
    rw [← hL]
    change ψ (Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (x * y)) = 1
    have he : Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (x * y) = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F (.inl v) (e.symm y v) := by
      apply Prod.ext
      · change e.symm (x * y) = Pi.single v (e.symm y v)
        rw [map_mul, show e.symm x = Pi.single v 1 from e.symm_apply_apply _]
        funext w
        change Pi.single v (1 : v.Completion) w * e.symm y w = Pi.single v (e.symm y v) w
        by_cases hw : w = v
        · subst w
          simp
        · simp [Pi.single_eq_of_ne hw]
      · rfl
    rw [he]
    exact hlocal _
  have hx : x = 0 := by
    apply hsep x
    intro y
    by_contra hzero
    have h := hchar ((1 / (2 * L (x * y))) • y)
    rw [mul_smul_comm, map_smul, smul_eq_mul] at h
    have he : 1 / (2 * L (x * y)) * L (x * y) = 1 / 2 := by
      field_simp [hzero]
    rw [he] at h
    exact realCharacter_half_ne_one h
  have he := congrArg e.symm hx
  change e.symm (e (Pi.single v 1)) = e.symm 0 at he
  erw [RingEquiv.symm_apply_apply, map_zero] at he
  have hcoord := congrArg (fun a : InfiniteAdeleRing F => a v) he
  change Pi.single v (1 : v.Completion) v = (0 : v.Completion) at hcoord
  rw [Pi.single_eq_same] at hcoord
  exact one_ne_zero hcoord

end

end OAI.RepresentationTheory.Theta.Adelic.ArchimedeanNontrivial
