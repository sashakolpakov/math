import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetExpansion
import OAI.RepresentationTheory.Weil.AdelicSplitting.MixedIntegerBasis

/-! # Coset Theta Primal -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! A rational finite coset theta sum is the corresponding shifted
Minkowski integer lattice sum, with an explicit bijective parametrization. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def CosetThetaPrimal.Construction.rationalCosetPosition (q : F) (a : Fin N → F) (r : Fin N → 𝓞 F) : Fin N → F :=
  fun i => a i + q * algebraMap (𝓞 F) F (r i)

theorem CosetThetaPrimal.Construction.rationalCosetPosition_injective (q : F) (hq : q ≠ 0) (a : Fin N → F) :
    Function.Injective (CosetThetaPrimal.Construction.rationalCosetPosition F N q a) := by
  intro r s h
  funext i
  apply IsFractionRing.injective (𝓞 F) F
  apply mul_left_cancel₀ hq
  exact add_left_cancel (congrFun h i)

theorem CosetThetaPrimal.Construction.rational_coset_mem_iff (q : F) (hq : q ≠ 0) (a x : Fin N → F) :
    FiniteCosets.Construction.finiteRationalPosition x - FiniteCosets.Construction.finiteRationalPosition a ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔
      ∃ r : Fin N → 𝓞 F, CosetThetaPrimal.Construction.rationalCosetPosition F N q a r = x := by
  have he : FiniteCosets.Construction.finiteRationalPosition x - FiniteCosets.Construction.finiteRationalPosition a = FiniteCosets.Construction.finiteRationalPosition (x - a) := by
    funext i
    exact (map_sub (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F)) (x i) (a i)).symm
  rw [he]
  change (fun i => algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) ((x - a) i)) ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔ _
  rw [FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff]
  constructor
  · intro h
    choose r hr using h
    refine ⟨r, funext (fun i => ?_)⟩
    change a i + q * algebraMap (𝓞 F) F (r i) = x i
    rw [hr i]
    exact add_sub_cancel _ _
  · rintro ⟨r, rfl⟩ i
    exact ⟨r i, by simp [CosetThetaPrimal.Construction.rationalCosetPosition]⟩

omit [NumberField F] in
theorem CosetThetaPrimal.Construction.rationalCosetPosition_mixed (q : F) (a : Fin N → F) (r : Fin N → 𝓞 F) :
    ThetaTest.Construction.mixedRationalPosition F N (CosetThetaPrimal.Construction.rationalCosetPosition F N q a r) =
      ThetaTest.Construction.mixedRationalPosition F N a + MixedFiniteDuality.Construction.mixedScalarIntegerPosition F N q r := by
  funext i
  exact map_add (mixedEmbedding F) _ _

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_coset_primal (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q : F) (hq : q ≠ 0) (a : Fin N → F) :
    (f.replaceFiniteByCoset F N q hq (FiniteCosets.Construction.finiteRationalPosition a)).theta F N =
      ∑' r : Fin N → 𝓞 F, f.mixedProductRapid F N
        (ThetaTest.Construction.mixedRationalPosition F N a + MixedFiniteDuality.Construction.mixedScalarIntegerPosition F N q r) := by
  let T (x : Fin N → F) := f.mixedProductRapid F N (ThetaTest.Construction.mixedRationalPosition F N x) *
    FiniteCosets.Construction.finitePositionCosetIndicator q hq (FiniteCosets.Construction.finiteRationalPosition a) (FiniteCosets.Construction.finiteRationalPosition x)
  have ht : (f.replaceFiniteByCoset F N q hq (FiniteCosets.Construction.finiteRationalPosition a)).theta F N = ∑' x, T x := by
    apply tsum_congr
    intro x
    rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.value_rational_factorization, RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset_finiteValue]
    rfl
  have hs : Function.support T ⊆ Set.range (CosetThetaPrimal.Construction.rationalCosetPosition F N q a) := by
    intro x hx
    apply (CosetThetaPrimal.Construction.rational_coset_mem_iff F N q hq a x).mp
    by_contra h
    apply hx
    change _ * _ = 0
    rw [FiniteCosets.Construction.finitePositionCosetIndicator, FiniteCosets.Construction.finitePositionIndicator, Set.indicator_of_notMem h, mul_zero]
  rw [ht, ← (CosetThetaPrimal.Construction.rationalCosetPosition_injective F N q hq a).tsum_eq hs]
  apply tsum_congr
  intro r
  have hm := (CosetThetaPrimal.Construction.rational_coset_mem_iff F N q hq a (CosetThetaPrimal.Construction.rationalCosetPosition F N q a r)).mpr ⟨r, rfl⟩
  change _ * FiniteCosets.Construction.finitePositionCosetIndicator q hq _ _ = _
  rw [FiniteCosets.Construction.finitePositionCosetIndicator, FiniteCosets.Construction.finitePositionIndicator, Set.indicator_of_mem hm, mul_one,
    CosetThetaPrimal.Construction.rationalCosetPosition_mixed]

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_coset_primal_coordinates (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (M : ℕ) (hM : 0 < M) (a : Fin N → F) :
    (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne') (FiniteCosets.Construction.finiteRationalPosition a)).theta F N =
      ∑' n : MixedIntegerBasis.Construction.MixedPositionIndex F N → ℤ, f.mixedProductRapid F N
        (ThetaTest.Construction.mixedRationalPosition F N a + (MixedIntegerBasis.Construction.mixedIntegerPositionBasis F N M hM).equivFun.symm (fun p => (n p : ℝ))) := by
  rw [f.theta_coset_primal F N]
  simp_rw [MixedIntegerBasis.Construction.mixedIntegerPositionBasis_integer_symm]
  exact ((MixedIntegerBasis.Construction.integerPositionCoordinates F N).symm.toEquiv.tsum_eq _).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
