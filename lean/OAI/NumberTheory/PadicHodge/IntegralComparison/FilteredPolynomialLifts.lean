import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Filtered Polynomial Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialLifts

noncomputable section

/-! A finite family of elements, and hence a monic polynomial, in a
filtered colimit of rings is defined at one stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat.{u})]

include hc

theorem representatives {ι : Type z} [Finite ι] (a : ι → c.pt) :
    ∃ (j : J) (b : ι → F.obj j), ∀ i, c.ι.app j (b i) = a i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose j b hb using fun i => Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) hc) (a i)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (i : ι) : j i ⟶ k := (hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).some
  refine ⟨k, fun i => F.map (f i) (b i), fun i => ?_⟩
  exact (ConcreteCategory.congr_hom (c.w (f i)) (b i)).trans (hb i)

theorem polynomial_lifts (p : Polynomial c.pt) :
    ∃ j, p ∈ Polynomial.lifts (c.ι.app j).hom := by
  classical
  obtain ⟨j, b, hb⟩ := representatives F c hc (fun i : p.support => p.coeff i)
  refine ⟨j, (Polynomial.lifts_iff_coeff_lifts p).mpr ?_⟩
  intro i
  by_cases hi : i ∈ p.support
  · exact ⟨b ⟨i, hi⟩, hb ⟨i, hi⟩⟩
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩

theorem monic_polynomial (p : Polynomial c.pt) (hp : p.Monic) :
    ∃ (j : J) (q : Polynomial (F.obj j)), q.map (c.ι.app j).hom = p ∧
      q.natDegree = p.natDegree ∧ q.Monic := by
  obtain ⟨j, hj⟩ := polynomial_lifts F c hc p
  obtain ⟨q, hq, hd, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hj hp
  exact ⟨j, q, hq, hd, hm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialLifts
