import Mathlib

/-! # Integral Geometry -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry

noncomputable section

/-!
# Actual integral-model geometry for crystalline comparison

The ring of integers is the valuation ring of the spectral extension of the
p-adic norm to a finite extension K. Generic and special fibers are categorical
base changes. The model carries only a scheme and its structure morphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped NNReal

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- The canonical extension of the p-adic valuation, expressed using the spectral norm. -/
def fieldValuation : Valuation K ℝ≥0 := by
  let _ : NormedField K := spectralNorm.normedField ℚ_[p] K
  let _ : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := K))
  exact (NormedField.toValued : Valued K ℝ≥0).v

theorem fieldValuation_algebraMap (a : ℚ_[p]) :
    fieldValuation p K (algebraMap ℚ_[p] K a) = ‖a‖₊ := by
  apply NNReal.eq
  exact spectralNorm_extends a

theorem fieldValuation_p : fieldValuation p K (p : K) = (p : ℝ≥0)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] K), fieldValuation_algebraMap]
  apply NNReal.eq
  change ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹
  exact Padic.norm_p

def ringOfIntegers : ValuationSubring K := (fieldValuation p K).valuationSubring

abbrev ResidueField := IsLocalRing.ResidueField (ringOfIntegers p K)

theorem p_mem_maximalIdeal : (p : ringOfIntegers p K) ∈ IsLocalRing.maximalIdeal (ringOfIntegers p K) := by
  apply (Valuation.mem_maximalIdeal_iff K (fieldValuation p K)).mpr
  change fieldValuation p K (p : K) < 1
  rw [fieldValuation_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

instance residueField_charP : CharP (IntegralGeometry.ResidueField p K) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue (ringOfIntegers p K))]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (p_mem_maximalIdeal p K)

/-- An integral model is the actual scheme over Spec(O_K), without cohomological assumptions. -/
abbrev IntegralModel := Over (Spec (.of (ringOfIntegers p K)))

section BaseChange

variable {S : Type u} [CommRing S]

def fiberFunctor (f : ringOfIntegers p K →+* S) :
    IntegralModel p K ⥤ Over (Spec (.of S)) :=
  Over.pullback (Scheme.Spec.map (CommRingCat.ofHom f).op)

abbrev fiber (f : ringOfIntegers p K →+* S) (M : IntegralModel p K) : Scheme :=
  ((fiberFunctor p K f).obj M).left

abbrev fiberStructureMap (f : ringOfIntegers p K →+* S) (M : IntegralModel p K) :
    fiber p K f M ⟶ Spec (.of S) := ((fiberFunctor p K f).obj M).hom

def fiberEndomorphism (f : ringOfIntegers p K →+* S) (M : IntegralModel p K) :
    End M →* End ((fiberFunctor p K f).obj M) :=
  Functor.mapEnd M (fiberFunctor p K f)

instance fiber_smooth (f : ringOfIntegers p K →+* S) (M : IntegralModel p K) [Smooth M.hom] :
    Smooth (fiberStructureMap p K f M) := by
  change Smooth (pullback.snd M.hom (Scheme.Spec.map (CommRingCat.ofHom f).op))
  infer_instance

instance fiber_proper (f : ringOfIntegers p K →+* S) (M : IntegralModel p K) [IsProper M.hom] :
    IsProper (fiberStructureMap p K f M) := by
  change IsProper (pullback.snd M.hom (Scheme.Spec.map (CommRingCat.ofHom f).op))
  infer_instance

end BaseChange

def genericFiberFunctor : IntegralModel p K ⥤ Over (Spec (.of K)) :=
  fiberFunctor p K (algebraMap (ringOfIntegers p K) K)

def specialFiberFunctor : IntegralModel p K ⥤ Over (Spec (.of (IntegralGeometry.ResidueField p K))) :=
  fiberFunctor p K (IsLocalRing.residue (ringOfIntegers p K))

abbrev genericFiber (M : IntegralModel p K) : Scheme := ((genericFiberFunctor p K).obj M).left

abbrev specialFiber (M : IntegralModel p K) : Scheme := ((specialFiberFunctor p K).obj M).left

def genericEndomorphism (M : IntegralModel p K) : End M →* End ((genericFiberFunctor p K).obj M) :=
  Functor.mapEnd M (genericFiberFunctor p K)

def specialEndomorphism (M : IntegralModel p K) : End M →* End ((specialFiberFunctor p K).obj M) :=
  Functor.mapEnd M (specialFiberFunctor p K)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry
