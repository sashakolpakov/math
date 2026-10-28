import OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredPolynomialRelations
import Mathlib.RingTheory.Etale.StandardEtale

/-! # Standard Etale Filtered Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleFilteredDescent

noncomputable section

/-! A standard etale presentation over a filtered ring colimit
descends to an actual finite stage, including its monicity and
the Bezout relation certifying etaleness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimitsOfShape J (forget CommRingCat.{u})]

private theorem pair_ext {R : Type u} [CommRing R] (P Q : StandardEtalePair R)
    (hf : P.f = Q.f) (hg : P.g = Q.g) : P = Q := by
  cases P
  cases Q
  cases hf
  cases hg
  rfl

include hc in
theorem exists_pair (P : StandardEtalePair c.pt) :
    ∃ (j : J) (Q : StandardEtalePair (F.obj j)), Q.map (c.ι.app j).hom = P := by
  obtain ⟨p₁, p₂, n, he⟩ := P.cond
  obtain ⟨j, f, hf, _, hm⟩ := FilteredPolynomialLifts.monic_polynomial F c hc P.f P.monic_f
  obtain ⟨k, q, hq⟩ := FilteredPolynomialRelations.polynomials F c hc
    (![P.g, p₁, p₂] : Fin 3 → Polynomial c.pt)
  let l := IsFiltered.max j k
  let a : j ⟶ l := IsFiltered.leftToMax j k
  let b : k ⟶ l := IsFiltered.rightToMax j k
  let f' := f.map (F.map a).hom
  let q' (i : Fin 3) := (q i).map (F.map b).hom
  have hf' : f'.map (c.ι.app l).hom = P.f := by
    rw [Polynomial.map_map]
    have hw : (c.ι.app l).hom.comp (F.map a).hom = (c.ι.app j).hom :=
      congrArg CommRingCat.Hom.hom (c.w a)
    rw [hw]
    exact hf
  have hq' (i : Fin 3) : (q' i).map (c.ι.app l).hom = ![P.g, p₁, p₂] i := by
    rw [Polynomial.map_map]
    have hw : (c.ι.app l).hom.comp (F.map b).hom = (c.ι.app k).hom :=
      congrArg CommRingCat.Hom.hom (c.w b)
    rw [hw]
    exact hq i
  have hrel : (f'.derivative * q' 1 + f' * q' 2).map (c.ι.app l).hom =
      ((q' 0) ^ n).map (c.ι.app l).hom := by
    simpa [Polynomial.map_add, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_pow, hf', hq'] using he
  obtain ⟨m, d, hd⟩ := FilteredPolynomialRelations.polynomial_eq F c hc l
    (f'.derivative * q' 1 + f' * q' 2) ((q' 0) ^ n) hrel
  let Q : StandardEtalePair (F.obj m) := {
    f := f'.map (F.map d).hom
    monic_f := (hm.map (F.map a).hom).map (F.map d).hom
    g := (q' 0).map (F.map d).hom
    cond := ⟨(q' 1).map (F.map d).hom, (q' 2).map (F.map d).hom, n, by
      simpa only [Polynomial.map_add, Polynomial.map_mul, ← Polynomial.derivative_map,
        Polynomial.map_pow] using hd⟩ }
  refine ⟨m, Q, ?_⟩
  have hw : (c.ι.app m).hom.comp (F.map d).hom = (c.ι.app l).hom :=
    congrArg CommRingCat.Hom.hom (c.w d)
  have hff : (Q.map (c.ι.app m).hom).f = P.f := by
    change (f'.map (F.map d).hom).map (c.ι.app m).hom = P.f
    rw [Polynomial.map_map, hw, hf']
  have hgg : (Q.map (c.ι.app m).hom).g = P.g := by
    change ((q' 0).map (F.map d).hom).map (c.ι.app m).hom = P.g
    rw [Polynomial.map_map, hw, hq']
    rfl
  exact pair_ext _ _ hff hgg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleFilteredDescent
