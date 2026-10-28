import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice
import OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter

/-! # Archimedean Dual Lattice -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice.Construction

noncomputable section

section

/-! Nondegeneracy of the archimedean character pairing, proved from the
actual local characters, and rationality of its matrix in an integral basis. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem archimedean_character_pairing_separates
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
    (x : mixedEmbedding.mixedSpace F)
    (hx : ∀ y, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (x * y) = 1) : x = 0 := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let u := e.symm x
  have hu : u = 0 := by
    funext v
    by_contra hv
    change u v ≠ 0 at hv
    obtain ⟨t, ht⟩ := hn v
    let y : InfiniteAdeleRing F := Pi.single v (t / u v)
    have he : ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (x * e y) = ArchimedeanAdeles.Construction.localAdd F (.inl v) t := by
      apply Prod.ext
      · change e.symm (x * e y) = Pi.single v t
        rw [map_mul, e.symm_apply_apply]
        funext w
        change u w * y w = Pi.single v t w
        by_cases hw : w = v
        · subst w
          simp [y, hv, div_eq_mul_inv, mul_left_comm]
        · simp [y, Pi.single_eq_of_ne hw]
      · rfl
    have hh := hx (e y)
    change ψ (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (x * e y)) = 1 at hh
    rw [he] at hh
    exact ht hh
  have hh := congrArg e hu
  simpa only [u, e.apply_symm_apply, map_zero] using hh

theorem archimedean_linear_pairing_separates
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x, ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ x = RealCharacters.LocalAnalysis.realCharacter 1 (L x))
    (x : mixedEmbedding.mixedSpace F) (hx : ∀ y, L (x * y) = 0) : x = 0 := by
  apply archimedean_character_pairing_separates F ψ hn x
  intro y
  rw [hL, hx, AddChar.map_zero_eq_one]

theorem archimedean_pairing_matrix_rational
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r))) :
    ∃ A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ,
      ∀ i j, (A i j : ℝ) =
        L (mixedEmbedding.latticeBasis F i * mixedEmbedding.latticeBasis F j) := by
  choose A hA using (fun i j => hL (RingOfIntegers.basis F i * RingOfIntegers.basis F j))
  refine ⟨A, fun i j => ?_⟩
  simpa only [mixedEmbedding.latticeBasis_apply, integralBasis_apply, map_mul] using hA i j

end

/-! The dual of the embedded integer lattice for the actual archimedean
character pairing consists of rational points. The proof uses its rational,
nondegenerate matrix and solves the corresponding rational linear system. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem archimedean_dual_integer_lattice_rational
    (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hsep : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0)
    (hrat : ∀ r : 𝓞 F, ∃ q : ℚ, (q : ℝ) = L (mixedEmbedding F (algebraMap (𝓞 F) F r)))
    (x : mixedEmbedding.mixedSpace F)
    (hx : ∀ r : 𝓞 F, RealCharacters.LocalAnalysis.realCharacter 1 (L (x * mixedEmbedding F (algebraMap (𝓞 F) F r))) = 1) :
    ∃ q : F, mixedEmbedding F q = x := by
  let b := mixedEmbedding.latticeBasis F
  let B : LinearMap.BilinForm ℝ (mixedEmbedding.mixedSpace F) := (LinearMap.mul ℝ _).compr₂ L
  have hBapply (s t : mixedEmbedding.mixedSpace F) : B s t = L (s * t) := rfl
  have hB : B.Nondegenerate := by
    constructor
    · exact hsep
    · intro y hy
      apply hsep y
      intro z
      simpa only [hBapply, mul_comm] using hy z
  obtain ⟨A, hA⟩ := archimedean_pairing_matrix_rational F L hrat
  have hAb (i j : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) : (A i j : ℝ) = L (b i * b j) := hA i j
  have hmatrix : LinearMap.BilinForm.toMatrix b B = A.map (algebraMap ℚ ℝ) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, hBapply]
    exact (hA i j).symm
  have hdetR := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet : A.det ≠ 0 := by
    intro h
    apply hdetR
    rw [hmatrix]
    change ((algebraMap ℚ ℝ).mapMatrix A).det = 0
    rw [← RingHom.map_det, h, map_zero]
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hx' (j : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      ∃ z : ℤ, (z : ℝ) = L (x * b j) := by
    apply (RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff _).mp
    simpa only [b, mixedEmbedding.latticeBasis_apply, integralBasis_apply] using hx (RingOfIntegers.basis F j)
  choose z hz using hx'
  obtain ⟨u, hu⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hunit) (fun j => (z j : ℚ))
  let q : F := ∑ i, u i • integralBasis F i
  have hq : mixedEmbedding F q = ∑ i, (u i : ℝ) • b i := by
    simp only [q, map_sum, map_rat_smul, b, mixedEmbedding.latticeBasis_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (Rat.cast_smul_eq_qsmul ℝ _ _).symm
  have hpair (j : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      B (mixedEmbedding F q) (b j) = B x (b j) := by
    rw [hq, map_sum, LinearMap.sum_apply]
    change (∑ i, B ((u i : ℝ) • b i) (b j)) = B x (b j)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have he := congrArg (fun f => (f j : ℝ)) hu
    simp only [Matrix.vecMul, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at he
    change (∑ i, (u i : ℝ) * L (b i * b j)) = L (x * b j)
    simp_rw [← hAb]
    exact he.trans (hz j)
  have heq : mixedEmbedding F q - x = 0 := by
    apply hsep
    intro y
    have hbzero (j : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) : B (mixedEmbedding F q - x) (b j) = 0 := by
      rw [map_sub, LinearMap.sub_apply, hpair, sub_self]
    change B (mixedEmbedding F q - x) y = 0
    rw [← b.sum_repr y, map_sum]
    simp only [map_smul, hbzero, smul_zero, Finset.sum_const_zero]
  exact ⟨q, sub_eq_zero.mp heq⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice.Construction
