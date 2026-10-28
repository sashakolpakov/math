import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
import OAI.Algorithms.SubexponentialSAT.LiftRing
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
# Canonical coordinates and binary encoding for the selected quartic quotient

The four-coordinate representation denotes the exact quotient by
`QuarticSearch.poly c`. Its inverse is mathematical canonical-remainder
extraction. Binary operations on already supplied coefficient words remain
the executable operations of `SubexpQuarticRing`; no runtime claim is made
for extracting coordinates from an abstract quotient value.
-/

namespace SubexponentialSAT.SubexpQuarticEncoding

open SubexpQuarticRing
open scoped BigOperators

/-- A four-field record and a function on Fin 4 contain the same data. -/
def quadEquiv (A : Type*) : Quad A ≃ (Fin 4 → A) where
  toFun := Quad.toFn
  invFun := Quad.ofFn
  left_inv a := by cases a; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

section Coordinates

variable {R : Type*} [CommRing R]

/-- Reindex the canonical quotient coordinates by a known degree. -/
noncomputable def coordinatesOfDegree {n : ℕ} (F : Polynomial R)
    (hF : F.Monic) (hdegree : F.natDegree = n) :
    LiftRing.Extension F ≃ (Fin n → R) :=
  hdegree ▸ (LiftRing.coordinates hF).toEquiv

@[simp] theorem coordinatesOfDegree_apply {n : ℕ} (F : Polynomial R)
    (hF : F.Monic) (hdegree : F.natDegree = n)
    (x : LiftRing.Extension F) (i : Fin n) :
    coordinatesOfDegree F hF hdegree x i = (LiftRing.remainder hF x).coeff i := by
  subst n
  rfl

@[simp] theorem coordinatesOfDegree_symm_apply {n : ℕ} (F : Polynomial R)
    (hF : F.Monic) (hdegree : F.natDegree = n) (a : Fin n → R) :
    (coordinatesOfDegree F hF hdegree).symm a =
      LiftRing.mk F (∑ i : Fin n, Polynomial.monomial i (a i)) := by
  subst n
  rfl

variable [Nontrivial R]

/-- Canonical coordinates of the actual monic quartic quotient. -/
noncomputable def quarticCoordinates (c : Fin 4 → R) :
    LiftRing.Extension (QuarticSearch.poly c) ≃ (Fin 4 → R) :=
  coordinatesOfDegree _ (QuarticSearch.poly_monic c) (QuarticSearch.poly_natDegree c)

/-- The record representation is equivalent to the exact polynomial quotient. -/
noncomputable def quotientEquiv (c : Fin 4 → R) :
    Quad R ≃ LiftRing.Extension (QuarticSearch.poly c) :=
  (quadEquiv R).trans (quarticCoordinates c).symm

@[simp] theorem quotientEquiv_apply (c : Fin 4 → R) (a : Quad R) :
    quotientEquiv c a = quotientDenote c a := by
  change (coordinatesOfDegree _ (QuarticSearch.poly_monic c)
    (QuarticSearch.poly_natDegree c)).symm (Quad.toFn a) = _
  rw [coordinatesOfDegree_symm_apply]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Quad.toFn, Matrix.cons_val_zero, Matrix.cons_val_succ, ← Polynomial.C_mul_X_pow_eq_monomial,
    pow_zero, mul_one, map_add, map_mul, map_pow,
    quotientDenote, denote, LiftRing.of, RingHom.comp_apply]
  ring

/-- No two different coefficient records denote the same quotient element. -/
theorem quotientDenote_injective (c : Fin 4 → R) :
    Function.Injective (quotientDenote c) := by
  intro a b hab
  apply (quotientEquiv c).injective
  simpa only [quotientEquiv_apply] using hab

/-- Every quotient class is denoted by a four-coordinate record. -/
theorem quotientDenote_surjective (c : Fin 4 → R) :
    Function.Surjective (quotientDenote c) := by
  intro x
  obtain ⟨a, ha⟩ := (quotientEquiv c).surjective x
  exact ⟨a, by simpa only [quotientEquiv_apply] using ha⟩

theorem quotientDenote_bijective (c : Fin 4 → R) :
    Function.Bijective (quotientDenote c) :=
  ⟨quotientDenote_injective c, quotientDenote_surjective c⟩

/-- Mathematical canonical coefficient extraction from an abstract quotient. -/
noncomputable def quotientCoefficients (c : Fin 4 → R)
    (x : LiftRing.Extension (QuarticSearch.poly c)) : Quad R :=
  (quotientEquiv c).symm x

/-- The inverse record contains exactly the four coefficients of the unique
degree-below-four remainder polynomial. -/
theorem quotientCoefficients_toFn (c : Fin 4 → R)
    (x : LiftRing.Extension (QuarticSearch.poly c)) (i : Fin 4) :
    Quad.toFn (quotientCoefficients c x) i =
      (LiftRing.remainder (QuarticSearch.poly_monic c) x).coeff i := by
  calc
    Quad.toFn (quotientCoefficients c x) i = quarticCoordinates c x i :=
      congrFun ((quadEquiv R).apply_symm_apply (quarticCoordinates c x)) i
    _ = _ := coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem quotientDenote_quotientCoefficients (c : Fin 4 → R)
    (x : LiftRing.Extension (QuarticSearch.poly c)) :
    quotientDenote c (quotientCoefficients c x) = x := by
  rw [← quotientEquiv_apply]
  exact (quotientEquiv c).apply_symm_apply x

@[simp] theorem quotientCoefficients_quotientDenote (c : Fin 4 → R) (a : Quad R) :
    quotientCoefficients c (quotientDenote c a) = a := by
  rw [← quotientEquiv_apply]
  exact (quotientEquiv c).symm_apply_apply a

end Coordinates

section BinaryEncoding

variable (p μ : ℕ) [Fact p.Prime]

/-- Exactly four fixed-width base-coefficient words, in increasing degree order. -/
def encodeQuad (a : Quad (ZMod (p ^ μ))) : List Bool :=
  SubexpLiftRing.encodeBase p μ a.c0 ++
  SubexpLiftRing.encodeBase p μ a.c1 ++
  SubexpLiftRing.encodeBase p μ a.c2 ++
  SubexpLiftRing.encodeBase p μ a.c3

omit [Fact (Nat.Prime p)] in
@[simp] theorem encodeQuad_length (a : Quad (ZMod (p ^ μ))) :
    (encodeQuad p μ a).length = 4 * μ * (Nat.log 2 p + 1) := by
  simp only [encodeQuad, List.length_append, SubexpLiftRing.encodeBase_length,
    SubexpLiftRing.baseWidth]
  ring

/-- Relation to the already verified fixed-width block concatenation. -/
theorem encodeQuad_eq_stack (hμ : 0 < μ) (a : Quad (ZMod (p ^ μ))) :
    encodeQuad p μ a =
      StackEncoding.encodeDataStack (SubexpLiftRing.baseCode p μ hμ)
        (List.ofFn (Quad.toFn a)) := by
  cases a
  simp [encodeQuad, Quad.toFn, List.ofFn_succ, SubexpLiftRing.baseCode,
    List.append_assoc]

theorem encodeQuad_injective (hμ : 0 < μ) :
    Function.Injective (encodeQuad p μ) := by
  intro a b hab
  rw [encodeQuad_eq_stack p μ hμ a, encodeQuad_eq_stack p μ hμ b] at hab
  have hlist := StackEncoding.encodeDataStack_injective
    (SubexpLiftRing.baseCode p μ hμ) hab
  exact (quadEquiv _).injective (List.ofFn_injective hlist)

/-- Positivity of the modulus exponent makes the prime-power base nontrivial. -/
theorem primePower_one_lt (hμ : 0 < μ) : 1 < p ^ μ :=
  Nat.one_lt_pow (Nat.ne_of_gt hμ) (Fact.out : p.Prime).one_lt

/-- Canonical binary representation of a quotient by any supplied monic quartic.
Coordinate extraction is noncomputable here; executable record arithmetic is
provided separately by SubexpQuarticRing. -/
noncomputable def encodeQuotient (hμ : 0 < μ) (c : Fin 4 → ZMod (p ^ μ))
    (x : LiftRing.Extension (QuarticSearch.poly c)) : List Bool := by
  letI : Fact (1 < p ^ μ) := ⟨primePower_one_lt p μ hμ⟩
  exact encodeQuad p μ (quotientCoefficients c x)

/-- A concrete coefficient record is encoded directly by its four words;
passing through the quotient does not change its representation. -/
@[simp] theorem encodeQuotient_quotientDenote (hμ : 0 < μ)
    (c : Fin 4 → ZMod (p ^ μ)) (a : Quad (ZMod (p ^ μ))) :
    encodeQuotient p μ hμ c (quotientDenote c a) = encodeQuad p μ a := by
  let _ : Fact (1 < p ^ μ) := ⟨primePower_one_lt p μ hμ⟩
  change encodeQuad p μ (quotientCoefficients c (quotientDenote c a)) = _
  rw [quotientCoefficients_quotientDenote]

@[simp] theorem encodeQuotient_length (hμ : 0 < μ)
    (c : Fin 4 → ZMod (p ^ μ)) (x : LiftRing.Extension (QuarticSearch.poly c)) :
    (encodeQuotient p μ hμ c x).length = 4 * μ * (Nat.log 2 p + 1) := by
  unfold encodeQuotient
  exact encodeQuad_length p μ _

theorem encodeQuotient_injective (hμ : 0 < μ) (c : Fin 4 → ZMod (p ^ μ)) :
    Function.Injective (encodeQuotient p μ hμ c) := by
  let _ : Fact (1 < p ^ μ) := ⟨primePower_one_lt p μ hμ⟩
  intro a b hab
  apply (quotientEquiv c).symm.injective
  exact encodeQuad_injective p μ hμ hab

/-- The selected ring is exactly the quartic whose coefficients the executable
search returned and then lifted; no alternate field presentation is selected. -/
abbrev SelectedRing :=
  LiftRing.Extension (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))

noncomputable def encodeSelected (hμ : 0 < μ) (x : SelectedRing p μ) : List Bool :=
  encodeQuotient p μ hμ (QuarticSearch.liftedCoefficients p μ) x

@[simp] theorem encodeSelected_length (hμ : 0 < μ) (x : SelectedRing p μ) :
    (encodeSelected p μ hμ x).length = 4 * μ * (Nat.log 2 p + 1) :=
  encodeQuotient_length p μ hμ _ x

theorem encodeSelected_injective (hμ : 0 < μ) :
    Function.Injective (encodeSelected p μ hμ) :=
  encodeQuotient_injective p μ hμ _

end BinaryEncoding

end SubexponentialSAT.SubexpQuarticEncoding

end OAI.Algorithms
