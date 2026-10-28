import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice
import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation

/-! # Annihilator -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Annihilator.Construction

noncomputable section

/-! The arithmetic self-annihilator argument for the actual adelic
character. Archimedean dual-lattice rationality and finite strong approximation
identify an adele annihilating the number field with a principal adele. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem adelic_mul_mixedAdelicAdd (a : ArchimedeanAdeles.Construction.Adeles F) (x : mixedEmbedding.mixedSpace F) :
    a * ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F x = ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * x) := by
  apply Prod.ext
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * x)
    rw [map_mul, RingEquiv.symm_apply_apply]
  · change a.2 * 0 = 0
    exact mul_zero _

theorem rational_annihilator_archimedean_rational
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
    (a : ArchimedeanAdeles.Construction.Adeles F) (ha : ∀ q : F, ψ (a * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∃ q : F, a.1 = algebraMap F (InfiniteAdeleRing F) q := by
  obtain ⟨L, hL, hrat⟩ := ArchimedeanCharacterLattice.Construction.exists_archimedean_linear_character_rational F ψ hc hu hp
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let χ := ψ.mulShift a
  have hcχ : Continuous χ := hc.comp (continuous_const.mul continuous_id)
  obtain ⟨M, hM, hχ⟩ := ArchimedeanCharacterLattice.Construction.archimedean_character_integer_multiple F χ hcχ (fun t => hu (a * t)) ha
  let x : mixedEmbedding.mixedSpace F := (M : mixedEmbedding.mixedSpace F) * e a.1
  have hx (r : 𝓞 F) : RealCharacters.LocalAnalysis.realCharacter 1
      (L (x * mixedEmbedding F (algebraMap (𝓞 F) F r))) = 1 := by
    rw [← hL]
    have hh := hχ r
    change ψ (a * ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F
      (mixedEmbedding F ((M : F) * algebraMap (𝓞 F) F r))) = 1 at hh
    rw [adelic_mul_mixedAdelicAdd, map_mul (mixedEmbedding F), map_natCast (mixedEmbedding F)] at hh
    change ψ (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (x * mixedEmbedding F (algebraMap (𝓞 F) F r))) = 1
    have he : x * mixedEmbedding F (algebraMap (𝓞 F) F r) =
        e a.1 * ((M : mixedEmbedding.mixedSpace F) * mixedEmbedding F (algebraMap (𝓞 F) F r)) := by
      dsimp only [x]
      ring
    rw [he]
    exact hh
  obtain ⟨q, hq⟩ := ArchimedeanDualLattice.Construction.archimedean_dual_integer_lattice_rational F L
    (ArchimedeanDualLattice.Construction.archimedean_linear_pairing_separates F ψ hn L hL) hrat x hx
  have hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨q / (M : F), ?_⟩
  apply e.injective
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have heq : mixedEmbedding F q = mixedEmbedding F (M : F) * e a.1 := by
    simpa only [map_natCast] using hq
  calc
    e a.1 = mixedEmbedding F ((M : F)⁻¹) * mixedEmbedding F q := by
      rw [heq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hMF, map_one, one_mul]
    _ = mixedEmbedding F (q / (M : F)) := by
      rw [← map_mul, div_eq_mul_inv, mul_comm]

theorem adelic_mul_localAdd (a : ArchimedeanAdeles.Construction.Adeles F) (v : ArchimedeanAdeles.Construction.Places F) (t : ArchimedeanAdeles.Construction.Completion F v) :
    a * ArchimedeanAdeles.Construction.localAdd F v t = ArchimedeanAdeles.Construction.localAdd F v (ArchimedeanAdeles.Construction.evaluate F v a * t) := by
  apply ArchimedeanAdeles.Construction.adeles_ext F
  intro w
  rw [map_mul]
  by_cases hw : w = v
  · subst w
    rw [ArchimedeanAdeles.Construction.evaluate_localAdd_same, ArchimedeanAdeles.Construction.evaluate_localAdd_same]
  · rw [ArchimedeanAdeles.Construction.evaluate_localAdd_other F hw, ArchimedeanAdeles.Construction.evaluate_localAdd_other F hw, mul_zero]

def finiteAdelicAdd : ArchimedeanAdeles.Construction.FiniteAdeles F →+ ArchimedeanAdeles.Construction.Adeles F where
  toFun t := (0, t)
  map_zero' := rfl
  map_add' x y := by
    change ((0 : InfiniteAdeleRing F), x + y) = (0 + 0, x + y)
    rw [add_zero]

theorem finiteAdelicAdd_continuous : Continuous (finiteAdelicAdd F) :=
  continuous_const.prodMk continuous_id

theorem rational_adelic_annihilator
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (hn : ∀ v : ArchimedeanAdeles.Construction.Places F, ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1)
    (a : ArchimedeanAdeles.Construction.Adeles F) :
    (∀ q : F, ψ (a * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) ↔
      ∃ r : F, algebraMap F (ArchimedeanAdeles.Construction.Adeles F) r = a := by
  constructor
  · intro ha
    obtain ⟨r, hr⟩ := rational_annihilator_archimedean_rational F ψ hc hu hp
      (fun v => hn (.inl v)) a ha
    let b : ArchimedeanAdeles.Construction.Adeles F := a - algebraMap F (ArchimedeanAdeles.Construction.Adeles F) r
    have hb0 : b.1 = 0 := by
      change a.1 - algebraMap F (InfiniteAdeleRing F) r = 0
      exact sub_eq_zero.mpr hr
    have hb (q : F) : ψ (b * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1 := by
      change ψ ((a - algebraMap F (ArchimedeanAdeles.Construction.Adeles F) r) * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1
      rw [sub_mul, ψ.map_sub_eq_div, ha, ← map_mul, hp, div_one]
    let f : ArchimedeanAdeles.Construction.FiniteAdeles F → ℂ := fun t => ψ (b * finiteAdelicAdd F t)
    have hi : Continuous (finiteAdelicAdd F) := finiteAdelicAdd_continuous F
    have hf : Continuous f := hc.comp (continuous_const.mul hi)
    have hfrat (q : F) : f (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) = 1 := by
      have he : b * finiteAdelicAdd F (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) =
          b * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q := by
        apply Prod.ext
        · change b.1 * 0 = b.1 * algebraMap F (InfiniteAdeleRing F) q
          rw [hb0, zero_mul, zero_mul]
        · rfl
      exact (congrArg ψ he).trans (hb q)
    have hfall : f = fun _ => 1 := (StrongApproximation.Construction.denseRange_rational_finiteAdeles F).equalizer hf continuous_const
      (funext hfrat)
    have hbzero : b = 0 := by
      apply Prod.ext
      · exact hb0
      · apply RestrictedProduct.ext
        intro v
        change b.2 v = 0
        by_contra hv
        obtain ⟨t, ht⟩ := hn (.inr v)
        have hh := congrFun hfall (RestrictedProduct.single
          (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v (t / b.2 v))
        change ψ (b * ArchimedeanAdeles.Construction.localAdd F (.inr v) (t / b.2 v)) = 1 at hh
        rw [adelic_mul_localAdd] at hh
        have he : ArchimedeanAdeles.Construction.evaluate F (.inr v) b * (t / b.2 v) = t := by
          change b.2 v * (t / b.2 v) = t
          simp [hv, div_eq_mul_inv, mul_left_comm]
        rw [he] at hh
        exact ht hh
    exact ⟨r, (sub_eq_zero.mp hbzero).symm⟩
  · rintro ⟨r, rfl⟩ q
    rw [← map_mul, hp]

theorem normalized_rational_adelic_annihilator
    (d : F) (hd : d ≠ 0) (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) (a : ArchimedeanAdeles.Construction.Adeles F) :
    (∀ q : F, C.ψ (a * algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) ↔
      ∃ r : F, algebraMap F (ArchimedeanAdeles.Construction.Adeles F) r = a :=
  rational_adelic_annihilator F C.ψ C.ψ_continuous C.ψ_unitary C.ψ_principal
    (fun v => NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D v) a

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Annihilator.Construction
