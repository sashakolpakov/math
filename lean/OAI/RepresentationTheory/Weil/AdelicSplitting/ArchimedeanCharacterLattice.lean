import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterConductor
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters

/-! # Archimedean Character Lattice -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction

noncomputable section

/-! Principal triviality and the actual finite conductor impose integral
values on the archimedean linear character functional. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis

variable (F : Type) [Field F] [NumberField F]

def mixedAdelicAdd : mixedEmbedding.mixedSpace F →+ ArchimedeanAdeles.Construction.Adeles F where
  toFun x := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0)
  map_zero' := by change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0, 0) = (0, 0); rw [map_zero]
  map_add' x y := by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x + y), 0) =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0 + 0)
    rw [map_add, add_zero]

theorem mixedAdelicAdd_continuous : Continuous (mixedAdelicAdd F) :=
  (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm.continuous.prodMk continuous_const

theorem mixedAdelicAdd_rational (q : F) :
    mixedAdelicAdd F (mixedEmbedding F q) = (algebraMap F (InfiniteAdeleRing F) q, 0) := by
  apply Prod.ext
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedEmbedding F q) = _
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      RingEquiv.symm_apply_apply]
  · rfl

def archimedeanCharacter (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
  ψ.compAddMonoidHom (mixedAdelicAdd F)

theorem exists_archimedean_linear_character
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) :
    ∃ L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      ∀ x, archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x) :=
  RealCharacters.LocalAnalysis.continuous_unitary_vector_character (mixedEmbedding.latticeBasis F) (archimedeanCharacter F ψ)
    (hc.comp (mixedAdelicAdd_continuous F)) (fun x => hu (mixedAdelicAdd F x))

theorem archimedean_character_integer_multiple
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ r : 𝓞 F,
      archimedeanCharacter F ψ (mixedEmbedding F ((M : F) * algebraMap (𝓞 F) F r)) = 1 := by
  obtain ⟨M, hM, hfin⟩ := FiniteCharacterConductor.Construction.exists_finite_character_conductor F ψ hc hu
  refine ⟨M, hM, fun r => ?_⟩
  let q : F := (M : F) * algebraMap (𝓞 F) F r
  have hf : ψ ((0, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) : ArchimedeanAdeles.Construction.Adeles F) = 1 := by
    have hh := hfin (IntegralAdeles.Construction.integerToFiniteIntegral F r)
    simpa only [q, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply] using! hh
  change ψ (mixedAdelicAdd F (mixedEmbedding F q)) = 1
  rw [mixedAdelicAdd_rational]
  have he : ((algebraMap F (InfiniteAdeleRing F) q, 0) : ArchimedeanAdeles.Construction.Adeles F) +
      (0, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) = algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q := by
    apply Prod.ext
    · change algebraMap F (InfiniteAdeleRing F) q + 0 = _
      rw [add_zero]
      rfl
    · change 0 + algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q = _
      rw [zero_add]
      rfl
  calc
    ψ ((algebraMap F (InfiniteAdeleRing F) q, 0) : ArchimedeanAdeles.Construction.Adeles F) =
        ψ ((algebraMap F (InfiniteAdeleRing F) q, 0) : ArchimedeanAdeles.Construction.Adeles F) *
          ψ ((0, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q) : ArchimedeanAdeles.Construction.Adeles F) := by rw [hf, mul_one]
    _ = ψ (((algebraMap F (InfiniteAdeleRing F) q, 0) : ArchimedeanAdeles.Construction.Adeles F) +
        (0, algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q)) := (ψ.map_add_eq_mul _ _).symm
    _ = ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) := congrArg ψ he
    _ = 1 := hp q

theorem exists_archimedean_linear_character_rational
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1)
    (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∃ L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ x, archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x)) ∧
      (∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r))) := by
  obtain ⟨L, hL⟩ := exists_archimedean_linear_character F ψ hc hu
  obtain ⟨M, hM, hchar⟩ := archimedean_character_integer_multiple F ψ hc hu hp
  refine ⟨L, hL, fun r => ?_⟩
  have hh := hchar r
  rw [hL, RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff] at hh
  obtain ⟨z, hz⟩ := hh
  have he : mixedEmbedding F ((M : F) * algebraMap (𝓞 F) F r) =
      M • mixedEmbedding F (algebraMap (𝓞 F) F r) := by
    rw [map_mul, map_natCast, nsmul_eq_mul]
  rw [he, map_nsmul, nsmul_eq_mul] at hz
  refine ⟨(z : ℚ) / (M : ℚ), ?_⟩
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, div_eq_iff]
  · simpa only [mul_comm] using hz
  · exact_mod_cast hM.ne'

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction
