import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarSequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Surjective Scalar Complex Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarComplexSequence

noncomputable section

/-! Degreewise quotient presentations of scalar images give an actual short exact sequence of complexes. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {K L T : CochainComplex (ModuleCat.{v} R) ℕ}
  (q : K ⟶ L) (hq : ∀ a, Function.Surjective (q.f a)) (r : R)
  (hk : ∀ a (x : K.X a), q.f a x = 0 ↔ r • x = 0)

def inclusion : L ⟶ K where
  f a := ModuleCat.ofHom (SurjectiveScalarSequence.inclusion (q.f a).hom (hq a) r (hk a))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq i y
    change K.d i j (SurjectiveScalarSequence.inclusion (q.f i).hom (hq i) r (hk i) (q.f i x)) =
      SurjectiveScalarSequence.inclusion (q.f j).hom (hq j) r (hk j) (L.d i j (q.f i x))
    rw [SurjectiveScalarSequence.inclusion_apply]
    have hq' : L.d i j (q.f i x) = q.f j (K.d i j x) := congrArg (fun f => f x) (q.comm i j)
    rw [hq', SurjectiveScalarSequence.inclusion_apply]
    exact (K.d i j).hom.map_smul r x

theorem inclusion_apply (a : ℕ) (x : K.X a) : (inclusion q hq r hk).f a (q.f a x) = r • x :=
  SurjectiveScalarSequence.inclusion_apply (q.f a).hom (hq a) r (hk a) x

variable (g : K ⟶ T) (hg : ∀ a (x : K.X a), g.f a x = 0 ↔ ∃ y : K.X a, r • y = x)

include hg in
theorem composition_zero : inclusion q hq r hk ≫ g = 0 := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact (SurjectiveScalarSequence.exact (q.f a).hom (hq a) r (hk a) (g.f a).hom (hg a)).apply_apply_eq_zero y

def sequence : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (inclusion q hq r hk) g (composition_zero q hq r hk g hg)

theorem shortExact (hgs : ∀ a, Function.Surjective (g.f a)) : (sequence q hq r hk g hg).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro a
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact (SurjectiveScalarSequence.exact (q.f a).hom (hq a) r (hk a) (g.f a).hom (hg a) x).mp hx
  · exact (ModuleCat.mono_iff_injective _).mpr
      (SurjectiveScalarSequence.injective (q.f a).hom (hq a) r (hk a))
  · exact (ModuleCat.epi_iff_surjective _).mpr (hgs a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarComplexSequence
