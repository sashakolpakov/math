import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction

/-! # Finite Annihilator -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteAnnihilator.Construction

noncomputable section

section

/-! The finite Fourier transform of a compact open rational coset has
one positive volume factor, the finite character phase, and the exact
local annihilator support. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis

local instance finiteCosetMeasurableSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)

local instance finiteCosetBorelSpace (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def finiteLocalCosetVolume (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).real
    (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v : Set (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N))

def finiteCosetAnnihilator (q : F) (hq : q ≠ 0) : Set (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  {ξ | ∀ v : HeightOneSpectrum (𝓞 F), (fun i => ξ i v) ∈
    CompactCharacter.LocalAnalysis.additiveAnnihilator (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
      (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v).toAddSubgroup}

variable (hμ : ∀ v : HeightOneSpectrum (𝓞 F),
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Characters.Construction.localAdditiveCharacter F ψ (.inr v))).IsAddHaarMeasure)

include hμ in
theorem finiteLocalCosetVolume_pos (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    0 < finiteLocalCosetVolume F N ψ q hq v := by
  let := hμ v
  exact LocalCosetFourier.Analysis.compactOpenSubgroup_volume_pos _ _ (FiniteLatticeFactors.Construction.finiteLocalScalarLattice_compact F N q hq v)

include hμ in
theorem finiteCoset_fourier_at (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : F) (hq : q ≠ 0) (b : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F)
    (v : HeightOneSpectrum (𝓞 F)) (ξ : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    (((f.replaceFiniteByCoset F N q hq b).act F N ψ a) (.inr v)).val ξ =
      if ξ ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
          (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v).toAddSubgroup then
        (finiteLocalCosetVolume F N ψ q hq v : ℂ) *
          Characters.Construction.localAdditiveCharacter F ψ (.inr v) (-Local.FunctionsMetaplectic.Construction.dot ξ (fun i => b i v)) else 0 := by
  let := hμ v
  exact (ha.2 (.inr v) ((f.replaceFiniteByCoset F N q hq b) (.inr v)) ξ).trans
    (LocalCosetFourier.Analysis.fourier_localCosetIndicator _ _ _ _ _)

include hμ in
theorem finiteLocalCosetVolume_eventually_one (a : Rational.Construction.RestrictedCover F N ψ)
    (ha : Rational.Construction.IsRationalFourier F N ψ a) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : F) (hq : q ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, finiteLocalCosetVolume F N ψ q hq v = 1 := by
  filter_upwards [((f.replaceFiniteByCoset F N q hq 0).act F N ψ a).unramified] with v hv
  have h := finiteCoset_fourier_at F N ψ hμ a ha f q hq 0 v 0
  rw [hv, Vacuum.Construction.finiteVacuum_zero, ite_eq_left (AddSubgroup.zero_mem _)] at h
  simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, mul_one] at h
  exact_mod_cast h.symm

include hμ in
theorem finiteCosetVolume_hasProd (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : F) (hq : q ≠ 0) :
    ∃ V : ℝ, 0 < V ∧ HasProd (fun v => (finiteLocalCosetVolume F N ψ q hq v : ℂ)) (V : ℂ) := by
  let s := (eventually_cofinite.mp (finiteLocalCosetVolume_eventually_one F N ψ hμ a ha f q hq)).toFinset
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) : finiteLocalCosetVolume F N ψ q hq v = 1 := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  refine ⟨∏ v ∈ s, finiteLocalCosetVolume F N ψ q hq v,
    Finset.prod_pos (fun v _ => finiteLocalCosetVolume_pos F N ψ hμ q hq v), ?_⟩
  have hh : HasProd (fun v => (finiteLocalCosetVolume F N ψ q hq v : ℂ))
      (∏ v ∈ s, (finiteLocalCosetVolume F N ψ q hq v : ℂ)) :=
    hasProd_prod_of_ne_finset_one (fun v hv => by rw [hout v hv, Complex.ofReal_one])
  simpa only [Complex.ofReal_prod] using hh

include hμ in
theorem finite_coset_fourier_value (hc : Continuous ψ)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : F) (hq : q ≠ 0) (V : ℝ)
    (hV : HasProd (fun v => (finiteLocalCosetVolume F N ψ q hq v : ℂ)) (V : ℂ))
    (b ξ : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ((f.replaceFiniteByCoset F N q hq b).act F N ψ a).finiteValue F N ξ =
      if ξ ∈ finiteCosetAnnihilator F N ψ q hq then
        (V : ℂ) * FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (-(∑ i, ξ i * b i)) else 0 := by
  by_cases hξ : ξ ∈ finiteCosetAnnihilator F N ψ q hq
  · rw [ite_eq_left hξ]
    apply HasProd.tprod_eq
    apply (hV.mul (FiniteCharacterProduct.Construction.localAdditiveCharacter_finite_dot_hasProd F ψ hc ξ b)).congr_fun
    intro v
    rw [finiteCoset_fourier_at F N ψ hμ a ha f q hq b v, ite_eq_left (hξ v)]
    rfl
  · rw [ite_eq_right hξ]
    apply tprod_of_exists_eq_zero
    change ¬ ∀ v, _ at hξ
    push Not at hξ
    obtain ⟨v, hv⟩ := hξ
    exact ⟨v, by rw [finiteCoset_fourier_at F N ψ hμ a ha f q hq b v, ite_eq_right hv]⟩

end

/-! The local annihilator condition equals annihilation of the actual
finite-adelic lattice. Strong approximation reduces it to rational points. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

open OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier.Analysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def finiteLocalPositionSingle (v : HeightOneSpectrum (𝓞 F))
    (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F :=
  fun i => (ArchimedeanAdeles.Construction.localAdd F (.inr v) (y i)).2

theorem finiteLocalPositionSingle_same (v : HeightOneSpectrum (𝓞 F))
    (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) (i : Fin N) :
    finiteLocalPositionSingle F N v y i v = y i :=
  ArchimedeanAdeles.Construction.evaluate_localAdd_same F (.inr v) (y i)

theorem finiteLocalPositionSingle_other (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v)
    (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) (i : Fin N) :
    finiteLocalPositionSingle F N v y i w = 0 :=
  ArchimedeanAdeles.Construction.evaluate_localAdd_other F (Sum.inr_injective.ne h) (y i)

theorem finiteLocalPositionSingle_mem_lattice (q : F) (hq : q ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
    (hy : y ∈ FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v) :
    finiteLocalPositionSingle F N v y ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq := by
  rw [FiniteLatticeFactors.Construction.finiteAdelicPositionLattice_local_iff F N q hq]
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [finiteLocalPositionSingle_same] using hy
  · simpa only [finiteLocalPositionSingle_other F N v w hw] using!
      (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq w).zero_mem

theorem finite_dot_character_hasProd (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (x y : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => Characters.Construction.localAdditiveCharacter F ψ (.inr v)
      (Local.FunctionsMetaplectic.Construction.dot (fun i => x i v) (fun i => y i v)))
      (FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, x i * y i)) := by
  have h := FiniteCharacterProduct.Construction.localAdditiveCharacter_finite_hasProd F ψ hc (∑ i, x i * y i)
  convert h using 1
  funext v
  congr 1
  let ev : ArchimedeanAdeles.Construction.FiniteAdeles F →+* v.adicCompletion F :=
    RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  have he : ev (∑ i, x i * y i) = ∑ i, ev (x i) * ev (y i) := by
    simp only [map_sum, map_mul]
  exact he.symm

theorem finite_dot_character_single (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) (v : HeightOneSpectrum (𝓞 F))
    (y : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, x i * finiteLocalPositionSingle F N v y i) =
      Characters.Construction.localAdditiveCharacter F ψ (.inr v) (Local.FunctionsMetaplectic.Construction.dot (fun i => x i v) y) := by
  let f (w : HeightOneSpectrum (𝓞 F)) := Characters.Construction.localAdditiveCharacter F ψ (.inr w)
    (Local.FunctionsMetaplectic.Construction.dot (fun i => x i w) (fun i => finiteLocalPositionSingle F N v y i w))
  have hout (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ ({v} : Finset _)) : f w = 1 := by
    have hne : w ≠ v := by simpa only [Finset.mem_singleton] using hw
    simp only [f, finiteLocalPositionSingle_other F N v w hne, Local.FunctionsMetaplectic.Construction.dot, mul_zero,
      Finset.sum_const_zero, AddChar.map_zero_eq_one]
  have hp : HasProd f (f v) := by
    simpa only [Finset.prod_singleton] using (hasProd_prod_of_ne_finset_one hout)
  have hh := (finite_dot_character_hasProd F N ψ hc x (finiteLocalPositionSingle F N v y)).unique hp
  simpa only [f, finiteLocalPositionSingle_same] using hh

theorem finiteCosetAnnihilator_iff (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (q : F) (hq : q ≠ 0) (ξ : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ξ ∈ finiteCosetAnnihilator F N ψ q hq ↔
      ∀ y ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq, FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, ξ i * y i) = 1 := by
  constructor
  · intro hξ y hy
    have hl := (FiniteLatticeFactors.Construction.finiteAdelicPositionLattice_local_iff F N q hq y).mp hy
    have hh := finite_dot_character_hasProd F N ψ hc ξ y
    have hone : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        Characters.Construction.localAdditiveCharacter F ψ (.inr v) (Local.FunctionsMetaplectic.Construction.dot (fun i => ξ i v) (fun i => y i v))) 1 := by
      convert (hasProd_one : HasProd (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) 1) using 1
      funext v
      exact hξ v _ (hl v)
    exact hh.unique hone
  · intro hξ v y hy
    have hh := hξ (finiteLocalPositionSingle F N v y)
      (finiteLocalPositionSingle_mem_lattice F N q hq v y hy)
    rw [finite_dot_character_single F N ψ hc] at hh
    exact hh

theorem finiteCosetAnnihilator_rational_iff (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (q : F) (hq : q ≠ 0) (ξ : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ξ ∈ finiteCosetAnnihilator F N ψ q hq ↔
      ∀ r : Fin N → F, FiniteCosets.Construction.finiteRationalPosition r ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq →
        FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, ξ i * FiniteCosets.Construction.finiteRationalPosition r i) = 1 := by
  rw [finiteCosetAnnihilator_iff F N ψ hc q hq ξ]
  constructor
  · intro h r hr
    exact h _ hr
  · intro h y hy
    by_contra hne
    let φ (x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) := FiniteCharacterProduct.Construction.finiteAdelicCharacter F ψ (∑ i, ξ i * x i)
    have hφ : Continuous φ := by
      apply (hc.comp (Annihilator.Construction.finiteAdelicAdd_continuous F)).comp
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
    have hopen : IsOpen {x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F |
        x ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq ∧ φ x ≠ 1} :=
      (FiniteLattices.Construction.finiteAdelicPositionLattice_isOpen q hq).inter (isOpen_ne.preimage hφ)
    obtain ⟨r, hr, hn⟩ := (FiniteCosets.Construction.denseRange_finiteRationalPosition (F := F) (ι := Fin N)).exists_mem_open
      hopen ⟨y, hy, hne⟩
    exact hn (h r hr)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteAnnihilator.Construction
