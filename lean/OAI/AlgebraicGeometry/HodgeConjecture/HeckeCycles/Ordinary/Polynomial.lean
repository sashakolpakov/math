import OAI.RepresentationTheory.Hecke.CubicRelation

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM

/-! Sum the literal ordinary-neighbor multisets and descend the resulting
polynomial through a faithful ring action. The native application derives
the detection and faithfulness hypotheses from its geometry. -/

def heckePolynomialValue (q : ℕ) {R : Type*} [Ring R] (Φ : R) (H : Fin 3 → R) : R :=
  Φ ^ 3 - H 0 * Φ ^ 2 + q • (H 1 * Φ) - q ^ 3 • H 2

theorem sum_map_nsmul {X A : Type*} [AddCommMonoid A]
    (f : X → A) (n : ℕ) (s : Multiset X) :
    ((n • s).map f).sum = n • (s.map f).sum :=
  map_nsmul (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom f)) n s

theorem polynomial_of_ordinary_neighbors
    (q : ℕ) (hq : q.Prime)
    {R S A O J : Type*} [Ring R] [Ring S] [AddCommGroup A]
    (sp : R →+* S) (hsp : Function.Injective sp)
    (act : S →+* AddMonoid.End A) (component : O → J) (a : O → A)
    (Φ : R) (H : Fin 3 → R) (X Z : O → O) (Y : O → Multiset O)
    (hXcomponent : ∀ x, component (X x) = component x)
    (hXY : ∀ x, (Y x).map X = Y (X x))
    (hXZ : ∀ x, X (Z x) = Z (X x))
    (hFrobenius : ∀ x, act (sp Φ) (a x) = a (X x))
    (hH : ∀ (i : Fin 3) (x y : O), component x = component y →
      act (sp (H i)) (a x - a y) =
        ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i x).map a).sum -
          ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i y).map a).sum)
    (hdetect : ∀ f : S, (∀ x y : O, component x = component y →
      act f (a x - a y) = 0) → f = 0) :
    Φ ^ 3 - H 0 * Φ ^ 2 + q • (H 1 * Φ) - q ^ 3 • H 2 = 0 := by
  have hpoly := RepresentationTheory.Hecke.CubicRelation.albanese_hecke_frobenius_relation q hq
    act component a (sp Φ) 1 (sp (H 0)) (sp (H 1)) (sp (H 2))
    X Z Y hXcomponent hFrobenius hXY hXZ
    (fun x y hxy => by
      simp only [one_mul]
      rw [hH 0 x y hxy]
      simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, sum_map_nsmul, smul_sub]
      abel)
    (fun x y hxy => by
      simp only [one_pow, one_mul]
      rw [hH 1 x y hxy]
      simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, sum_map_nsmul, smul_sub]
      abel)
    (fun x y hxy => by
      simp only [one_pow, one_mul]
      rw [hH 2 x y hxy]
      simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors]) hdetect
  apply hsp
  simpa only [map_sub, map_add, map_mul, map_pow, map_nsmul, map_zero,
    one_pow, one_mul] using hpoly

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM
