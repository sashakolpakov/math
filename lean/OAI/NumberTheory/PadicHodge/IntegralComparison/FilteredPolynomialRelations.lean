import OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialLifts

/-! # Filtered Polynomial Relations -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialRelations

noncomputable section

/-! Finite systems of coefficient equalities descend in filtered
ring colimits. In particular, equality of two polynomials at the
limit holds at a single later stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimitsOfShape J (forget CommRingCat.{u})]

include hc

theorem finite_equalities {ι : Type z} [Fintype ι] (j : J)
    (a b : ι → F.obj j) (h : ∀ i, c.ι.app j (a i) = c.ι.app j (b i)) :
    ∃ (k : J) (f : j ⟶ k), ∀ i, F.map f (a i) = F.map f (b i) := by
  classical
  have aux (s : Finset ι) : ∃ (k : J) (f : j ⟶ k),
      ∀ i ∈ s, F.map f (a i) = F.map f (b i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | @insert i s _hi ih =>
      obtain ⟨k, f, hf⟩ := ih
      have he : c.ι.app k (F.map f (a i)) = c.ι.app k (F.map f (b i)) := by
        exact (ConcreteCategory.congr_hom (c.w f) (a i)).trans
          ((h i).trans (ConcreteCategory.congr_hom (c.w f) (b i)).symm)
      obtain ⟨l, g, hg⟩ := (hc.eq_iff' (F.map f (a i)) (F.map f (b i))).mp he
      refine ⟨l, f ≫ g, ?_⟩
      intro t ht
      rw [F.map_comp]
      change F.map g (F.map f (a t)) = F.map g (F.map f (b t))
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hg
      · rw [hf t ht]
  obtain ⟨k, f, hf⟩ := aux Finset.univ
  exact ⟨k, f, fun i => hf i (Finset.mem_univ i)⟩

theorem polynomial_eq (j : J) (p q : Polynomial (F.obj j))
    (h : p.map (c.ι.app j).hom = q.map (c.ι.app j).hom) :
    ∃ (k : J) (f : j ⟶ k), p.map (F.map f).hom = q.map (F.map f).hom := by
  classical
  let s := p.support ∪ q.support
  obtain ⟨k, f, hf⟩ := finite_equalities F c hc j
    (fun i : s => p.coeff i) (fun i : s => q.coeff i)
    (fun i => by
      have hi := congrArg (fun r : Polynomial c.pt => r.coeff i) h
      simpa only [Polynomial.coeff_map] using hi)
  refine ⟨k, f, ?_⟩
  ext n
  by_cases hn : n ∈ s
  · simpa only [Polynomial.coeff_map] using hf ⟨n, hn⟩
  · have hp : n ∉ p.support := fun ht => hn (Finset.mem_union_left _ ht)
    have hq : n ∉ q.support := fun ht => hn (Finset.mem_union_right _ ht)
    simp only [Polynomial.coeff_map, Polynomial.notMem_support_iff.mp hp,
      Polynomial.notMem_support_iff.mp hq]

theorem polynomials {ι : Type z} [Fintype ι] (p : ι → Polynomial c.pt) :
    ∃ (j : J) (q : ι → Polynomial (F.obj j)),
      ∀ i, (q i).map (c.ι.app j).hom = p i := by
  classical
  have hp (i : ι) : ∃ j, ∃ q : Polynomial (F.obj j),
      q.map (c.ι.app j).hom = p i := by
    obtain ⟨j, hj⟩ := FilteredPolynomialLifts.polynomial_lifts F c hc (p i)
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (p i)).mp hj
    exact ⟨j, q, hq⟩
  choose j q hq using hp
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (i : ι) : j i ⟶ k := (hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).some
  refine ⟨k, fun i => (q i).map (F.map (f i)).hom, fun i => ?_⟩
  rw [Polynomial.map_map]
  have hw : (c.ι.app k).hom.comp (F.map (f i)).hom = (c.ι.app (j i)).hom :=
    congrArg CommRingCat.Hom.hom (c.w (f i))
  rw [hw, hq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialRelations
