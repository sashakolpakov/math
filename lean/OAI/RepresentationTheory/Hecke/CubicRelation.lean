import Mathlib

/-! # Cubic Relation -/

namespace OAI.RepresentationTheory.Hecke.CubicRelation

/-
Interface-level statement following OrdinaryCharacter. R models the integral
endomorphism ring of the specialized Albanese product, A its group of
geometric points, and O its ordinary source points. Multiplication in R
is composition; q • denotes repeated addition. The geometric realization
from good completely split reduction, including Néron specialization and
detection by ordinary Albanese differences, remains to be supplied.
The deduction below uses only the explicit target hypotheses. OrdinaryCharacter and
HomExtension are unnecessary once specialization, the point identities, and
faithful detection are supplied. No additional substantive assumption is
imposed, and no committed statement stub is imported.
-/

/--
Model:
* R is the integral endomorphism ring of the specialized Albanese product.
* A is its group of geometric points.
* O consists of ordinary points, with component map and Albanese map a.
* Φ, C0, T1, T2, T3 are the specialized geometric operators.
* hdetect expresses faithfulness on ordinary Albanese differences.
-/
theorem albanese_hecke_frobenius_relation
    (q : ℕ) (_hq : q.Prime)
    {R A O J : Type*}
    [Ring R] [AddCommGroup A]
    (act : R →+* AddMonoid.End A)
    (component : O → J)
    (a : O → A)
    (Φ C0 T1 T2 T3 : R)
    (X Z : O → O)
    (Y : O → Multiset O)
    (hXcomponent : ∀ x, component (X x) = component x)
    (hFrobenius : ∀ x, act Φ (a x) = a (X x))
    (_hXY : ∀ x, (Y x).map X = Y (X x))
    (_hXZ : ∀ x, X (Z x) = Z (X x))
    (hT1 : ∀ x y, component x = component y →
      act (C0 * T1) (a x - a y) =
        a (X x) - a (X y) +
          q • (((Y x).map a).sum - ((Y y).map a).sum))
    (hT2 : ∀ x y, component x = component y →
      act (C0 ^ 2 * T2) (a x - a y) =
        ((Y (X x)).map a).sum - ((Y (X y)).map a).sum +
          q ^ 2 • (a (Z x) - a (Z y)))
    (hT3 : ∀ x y, component x = component y →
      act (C0 ^ 3 * T3) (a x - a y) =
        a (Z (X x)) - a (Z (X y)))
    (hdetect : ∀ f : R,
      (∀ x y, component x = component y →
        act f (a x - a y) = 0) → f = 0) :
    Φ ^ 3 - C0 * T1 * Φ ^ 2 +
      q • (C0 ^ 2 * T2 * Φ) -
      q ^ 3 • (C0 ^ 3 * T3) = 0 := by
  apply hdetect
  intro x y hxy
  have hxy1 : component (X x) = component (X y) := by
    simpa only [hXcomponent] using hxy
  have hxy2 : component (X (X x)) = component (X (X y)) := by
    simpa only [hXcomponent] using hxy
  have hmul (f g : R) (b : A) : act (f * g) b = act f (act g b) := by
    rw [map_mul]
    rfl
  have hsub (f g : R) (b : A) : act (f - g) b = act f b - act g b := by
    rw [map_sub]
    rfl
  have hadd (f g : R) (b : A) : act (f + g) b = act f b + act g b := by
    rw [map_add]
    rfl
  have hsmul (n : ℕ) (f : R) (b : A) : act (n • f) b = n • act f b := by
    rw [map_nsmul]
    rfl
  have hpow (n : ℕ) (z : O) :
      act (Φ ^ n) (a z) = a (X^[n] z) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', hmul, ih, hFrobenius, Function.iterate_succ_apply']
  have hpow_sub (n : ℕ) (z w : O) :
      act (Φ ^ n) (a z - a w) = a (X^[n] z) - a (X^[n] w) := by
    rw [map_sub, hpow, hpow]
  have hφ (z w : O) : act Φ (a z - a w) = a (X z) - a (X w) := by
    rw [map_sub, hFrobenius, hFrobenius]
  simp only [hsub, hadd, hsmul]
  rw [hmul (C0 * T1), hmul (C0 ^ 2 * T2), hpow_sub, hpow_sub, hφ]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [hT1 _ _ hxy2, hT2 _ _ hxy1, hT3 _ _ hxy]
  simp only [smul_add, smul_smul, ← pow_succ']
  abel

/-!
## Explicit graph input propositions

These are the full proposition types of the supplied OrdinaryCharacter and HomExtension
specifications, copied without importing or invoking their proof stubs.
The conditional entry point below names both inputs. Neither is needed
by this target: its hT1/hT2/hT3 and hdetect already expose the specialized
point identities and detection required for the deduction. The primality
and ordinary-operator commutation hypotheses are likewise retained from
the target but unused in the cancellation. There are no new substantive
hypotheses in the direct theorem above.
-/

/-- Pairs of points in the same component. -/
abbrev ComponentPairs {S J : Type*} (component : S → J) :=
  {p : S × S // component p.1 = component p.2}

/-- The three neighbor multisets in (8), preserving multiplicities. -/
def ordinaryRawNeighbors {O : Type*}
    (q : ℕ) (X Z : O → O) (Y : O → Multiset O) :
    Fin 3 → O → Multiset O :=
  ![fun x => ({X x} : Multiset O) + q • Y x,
    fun x => Y (X x) + q ^ 2 • ({Z x} : Multiset O),
    fun x => ({Z (X x)} : Multiset O)]

def OrdinaryCharacterInput : Prop := ∀
    (q : ℕ) (_hq : q.Prime)
    {J Sη Sκ Aη Aκ Rη Rκ : Type*}
    [AddCommGroup Aη] [AddCommGroup Aκ]
    [Ring Rη] [Ring Rκ]
    (component : Sκ → J)
    [TopologicalSpace (ComponentPairs component)]
    (ordinary : Set Sκ)
    (aη : Sη → Aη) (aκ : Sκ → Aκ)
    (reducePoint : Sη → Sκ)
    (reduceAlb : Aη →+ Aκ)
    (actη : Rη →+* AddMonoid.End Aη)
    (actκ : Rκ →+* AddMonoid.End Aκ)
    (specialize : Rη →+* Rκ)
    (H : Fin 3 → Rη)
    (neighbors : Fin 3 → Sη → Multiset Sη)
    (Φ : Rκ)
    (X Z : ordinary → ordinary)
    (Y : ordinary → Multiset ordinary)

    (_hspecialize : ∀ (f : Rη) (b : Aη),
      reduceAlb (actη f b) =
        actκ (specialize f) (reduceAlb b))
    (_halbanese : ∀ x : Sη,
      reduceAlb (aη x) = aκ (reducePoint x))
    (_hlifts : ∀ x : ordinary,
      ∃ xη : Sη, reducePoint xη = x.val)

    (_hgeneric : ∀ (i : Fin 3) (x y : Sη),
      component (reducePoint x) = component (reducePoint y) →
      actη (H i) (aη x - aη y) =
        ((neighbors i x).map aη).sum -
        ((neighbors i y).map aη).sum)

    (_hneighbors : ∀ (i : Fin 3) (x : ordinary) (xη : Sη),
      reducePoint xη = x.val →
      (neighbors i xη).map reducePoint =
        (ordinaryRawNeighbors q X Z Y i x).map
          (fun z : ordinary => z.val))

    (_hXcomponent : ∀ x : ordinary,
      component (X x).val = component x.val)
    (_hXY : ∀ x : ordinary, (Y x).map X = Y (X x))
    (_hXZ : ∀ x : ordinary, X (Z x) = Z (X x))
    (_hFrobenius : ∀ x : ordinary,
      actκ Φ (aκ x.val) = aκ (X x).val)

    (_hdense : Dense
      {p : ComponentPairs component |
        p.val.1 ∈ ordinary ∧ p.val.2 ∈ ordinary})
    (_hclosed : ∀ f : Rκ,
      IsClosed
        {p : ComponentPairs component |
          actκ f (aκ p.val.1 - aκ p.val.2) = 0})
    (_hgenerate :
      AddSubgroup.closure
        (Set.range (fun p : ComponentPairs component =>
          aκ p.val.1 - aκ p.val.2)) = ⊤)
    (_hfaithful : Function.Injective actκ),

    let Hbar : Fin 3 → Rκ := fun i => specialize (H i)

    (∀ (i : Fin 3) (x y : ordinary),
      component x.val = component y.val →
      actκ (Hbar i) (aκ x.val - aκ y.val) =
        ((ordinaryRawNeighbors q X Z Y i x).map
          (fun z : ordinary => aκ z.val)).sum -
        ((ordinaryRawNeighbors q X Z Y i y).map
          (fun z : ordinary => aκ z.val)).sum) ∧

    (Φ ^ 3 - Hbar 0 * Φ ^ 2 +
      q • (Hbar 1 * Φ) - q ^ 3 • Hbar 2 = 0) ∧

    (∀ i : Fin 3, Commute (Hbar i) Φ)

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

universe u

def HomExtensionInput : Prop := ∀
    {R K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A B : Over (Spec (CommRingCat.of R)))
    [GrpObj A] [IsCommMonObj A]
    [GrpObj B] [IsCommMonObj B]
    [IsProper A.hom] [Smooth A.hom]
    [GeometricallyConnected A.hom]
    [IsProper B.hom] [Smooth B.hom]
    [GeometricallyConnected B.hom],
    let η := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let genericFiber := Over.pullback η
    ∀ fK : genericFiber.obj A ⟶ genericFiber.obj B,
      IsMonHom fK →
        ∃! f : A ⟶ B,
          IsMonHom f ∧ genericFiber.map f = fK

theorem albanese_hecke_frobenius_relation_conditional
    (_hC4_17 : OrdinaryCharacterInput)
    (_hE54 : HomExtensionInput)
    (q : ℕ) (hq : q.Prime)
    {R A O J : Type*}
    [Ring R] [AddCommGroup A]
    (act : R →+* AddMonoid.End A)
    (component : O → J)
    (a : O → A)
    (Φ C0 T1 T2 T3 : R)
    (X Z : O → O)
    (Y : O → Multiset O)
    (hXcomponent : ∀ x, component (X x) = component x)
    (hFrobenius : ∀ x, act Φ (a x) = a (X x))
    (hXY : ∀ x, (Y x).map X = Y (X x))
    (hXZ : ∀ x, X (Z x) = Z (X x))
    (hT1 : ∀ x y, component x = component y →
      act (C0 * T1) (a x - a y) =
        a (X x) - a (X y) +
          q • (((Y x).map a).sum - ((Y y).map a).sum))
    (hT2 : ∀ x y, component x = component y →
      act (C0 ^ 2 * T2) (a x - a y) =
        ((Y (X x)).map a).sum - ((Y (X y)).map a).sum +
          q ^ 2 • (a (Z x) - a (Z y)))
    (hT3 : ∀ x y, component x = component y →
      act (C0 ^ 3 * T3) (a x - a y) =
        a (Z (X x)) - a (Z (X y)))
    (hdetect : ∀ f : R,
      (∀ x y, component x = component y →
        act f (a x - a y) = 0) → f = 0) :
    Φ ^ 3 - C0 * T1 * Φ ^ 2 +
      q • (C0 ^ 2 * T2 * Φ) -
      q ^ 3 • (C0 ^ 3 * T3) = 0 := by
  exact albanese_hecke_frobenius_relation q hq act component a Φ C0 T1 T2 T3
    X Z Y hXcomponent hFrobenius hXY hXZ hT1 hT2 hT3 hdetect

end OAI.RepresentationTheory.Hecke.CubicRelation
