import Mathlib

/-! # Arithmetic Quotient Equations Data -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

noncomputable section

section

/-! Concrete data for ArithmeticQuotient, shared with its statement without importing a proof stub.
The definitions retain the committed statement's meanings and names. -/

open scoped BigOperators _root_.Manifold Classical

variable {E : Type*} [Field E] [NumberField E]
  [NumberField.IsCMField E]

abbrev Vec (K : Type*) := Fin 3 → K
abbrev Mat (K : Type*) := Matrix (Fin 3) (Fin 3) K

-- Hermitian form linear in its first argument.
def hermitian (b : E) (x y : Vec E) : E :=
  ∑ i, (if i = 2 then b else 1) * x i *
    NumberField.IsCMField.complexConj E (y i)

def complexHermitian (b : E) (μ : E →+* ℂ)
    (x y : Vec ℂ) : ℂ :=
  ∑ i, (if i = 2 then μ b else 1) * x i * star (y i)

-- Principal level N for the lattice O_E^3 in SU(hermitian b)(F).
def principalLevel (b : E) (N : ℕ) (g : Mat E) : Prop :=
  g.det = 1 ∧
  (∀ x y : Vec E,
    hermitian b (g.mulVec x) (g.mulVec y) =
      hermitian b x y) ∧
  ∃ B : Mat (NumberField.RingOfIntegers E),
    ∀ i j,
      g i j - (1 : Mat E) i j =
        (N : E) * (B i j : E)

def NegativeVectors (b : E) (μ : E →+* ℂ) :=
  {z : Vec ℂ // (complexHermitian b μ z z).re < 0}

/-- The negative cone has the topology induced from complex three-space. -/
instance negativeVectorsTopologicalSpace (b : E) (μ : E →+* ℂ) :
    TopologicalSpace (NegativeVectors b μ) :=
  inferInstanceAs (TopologicalSpace
    {z : Vec ℂ // (complexHermitian b μ z z).re < 0})

-- Quotienting also by nonzero scalars passes from vectors to lines.
def orbitRelation (b : E) (μ : E →+* ℂ) (N : ℕ)
    (z w : NegativeVectors b μ) : Prop :=
  ∃ g : Mat E, principalLevel b N g ∧
    ∃ t : ℂ, t ≠ 0 ∧
      ∀ i, w.val i = t * ∑ j, μ (g i j) * z.val j

-- An ambient extension of the projection, used only at negative vectors.
def projection (b : E) (μ : E →+* ℂ)
    (R : Setoid (NegativeVectors b μ))
    (z₀ : NegativeVectors b μ) (z : Vec ℂ) : Quotient R :=
  if hz : (complexHermitian b μ z z).re < 0 then
    Quotient.mk R ⟨z, hz⟩
  else
    Quotient.mk R z₀

end

section

/-! The actual special unitary matrix groups and their equations. The group
over E uses CM conjugation; its complex realizations use ordinary conjugation.
Form preservation is equivalent to nine explicit degree-two equations. -/

open scoped BigOperators Classical

abbrev SL (K : Type*) [CommRing K] := Matrix.SpecialLinearGroup (Fin 3) K

section Ring
variable {K : Type*} [CommRing K]

def diagonalCoefficient (b : K) (i : Fin 3) : K := if i = 2 then b else 1

def form (c : K →+* K) (b : K) (x y : Vec K) : K :=
  ∑ i, diagonalCoefficient b i * x i * c (y i)

lemma form_axis (c : K →+* K) (b : K) (i j : Fin 3) :
    form c b (Pi.single i 1) (Pi.single j 1) =
      if i = j then diagonalCoefficient b i else 0 := by
  by_cases h : i = j
  · subst j
    simp [form, Pi.single_apply, apply_ite]
  · simp [form, Pi.single_apply, apply_ite, h, Ne.symm h]

/-- The determinant-one isometries of the displayed sesquilinear form. -/
def unitarySubgroup (c : K →+* K) (b : K) : Subgroup (SL K) where
  carrier := {g | ∀ x y : Vec K,
    form c b (Matrix.SpecialLinearGroup.toLin' g x)
      (Matrix.SpecialLinearGroup.toLin' g y) = form c b x y}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x y
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg x y
    have h := hg (Matrix.SpecialLinearGroup.toLin' g⁻¹ x)
      (Matrix.SpecialLinearGroup.toLin' g⁻¹ y)
    have hc (z : Vec K) :
        Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' g⁻¹ z) = z := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hc] using h.symm

abbrev SU (c : K →+* K) (b : K) := ↥(unitarySubgroup c b)

def matrixOf (c : K →+* K) (b : K) : SU c b →* Mat K :=
  { toFun := fun g => (g.val : Mat K)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

lemma form_mulVec (c : K →+* K) (b : K) (g : Mat K) (x y : Vec K) :
    form c b (g.mulVec x) (g.mulVec y) =
      ∑ i, ∑ j, (∑ k, diagonalCoefficient b k * g k i * c (g k j)) * x i * c (y j) := by
  simp only [form, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The finite system of equations defining form preservation. -/
lemma unitary_iff_columns (c : K →+* K) (b : K) (g : SL K) :
    g ∈ unitarySubgroup c b ↔
      ∀ i j : Fin 3,
        (∑ k, diagonalCoefficient b k * g k i * c (g k j)) =
          if i = j then diagonalCoefficient b i else 0 := by
  constructor
  · intro hg i j
    have h := hg (Pi.single i 1) (Pi.single j 1)
    rw [form_axis] at h
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_single, form] using h
  · intro hg x y
    change form c b ((g : Mat K).mulVec x) ((g : Mat K).mulVec y) = _
    rw [form_mulVec]
    simp [hg, form]

end Ring

section Map
variable {K L : Type*} [CommRing K] [CommRing L]

/-- Scalar extension along an embedding commuting with the two involutions. -/
def unitaryMap (c : K →+* K) (d : L →+* L) (b : K) (f : K →+* L)
    (hc : ∀ x : K, f (c x) = d (f x)) : SU c b →* SU d (f b) where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.val, by
    apply (unitary_iff_columns d (f b) _).mpr
    intro i j
    have h := congrArg f ((unitary_iff_columns c b g.val).mp g.property i j)
    simpa [diagonalCoefficient, map_sum, map_mul, hc, apply_ite] using h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ g.val h.val

end Map

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

/-- F-rational points of SU(diag(1,1,b)), for a conjugation-fixed b. -/
abbrev RationalSU (b : E) :=
  SU (NumberField.IsCMField.complexConj E).toRingHom b

/-- The special unitary real Lie group at the embedding μ. -/
abbrev ArchimedeanSU (b : E) (μ : E →+* ℂ) := SU (starRingEnd ℂ) (μ b)

def infinitePlaceMap (b : E) (μ : E →+* ℂ) : RationalSU b →* ArchimedeanSU b μ :=
  unitaryMap _ _ b μ (NumberField.IsCMField.complexEmbedding_complexConj E μ)

lemma rationalSU_preserves (b : E) (g : RationalSU b) (x y : Vec E) :
    hermitian b ((matrixOf _ b g).mulVec x) ((matrixOf _ b g).mulVec y) =
      hermitian b x y := g.property x y

lemma infinitePlaceMap_injective (b : E) (μ : E →+* ℂ) :
    Function.Injective (infinitePlaceMap b μ) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply μ.injective
  exact congrArg (fun z : ArchimedeanSU b μ => z.val i j) he

end

section

/-! An explicit quadratic presentation of E over E⁺. This provides the two
real coordinates needed to write the unitary group as polynomial equations
over the actual totally real field. -/

open scoped Classical
open _root_.NumberField

abbrev RealField (E : Type*) [Field E] := maximalRealSubfield E

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

theorem exists_imaginary_generator :
    ∃ δ : E, δ ≠ 0 ∧ IsCMField.complexConj E δ = -δ := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  refine ⟨x - IsCMField.complexConj E x, ?_, ?_⟩
  · intro h
    exact hx (sub_eq_zero.mp h).symm
  · simp only [map_sub, IsCMField.complexConj_apply_apply, neg_sub]

def imaginarySquare (δ : E) (hδ : IsCMField.complexConj E δ = -δ) : RealField E :=
  ⟨δ ^ 2, (IsCMField.complexConj_eq_self_iff E _).mp (by simp [map_pow, hδ])⟩

def realCoordinate (x : E) : RealField E :=
  ⟨(x + IsCMField.complexConj E x) / 2,
    (IsCMField.complexConj_eq_self_iff E _).mp (by
      simp [map_div₀, map_add, map_ofNat, IsCMField.complexConj_apply_apply, add_comm])⟩

def imaginaryCoordinate (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (x : E) : RealField E :=
  ⟨(x - IsCMField.complexConj E x) / (2 * δ),
    (IsCMField.complexConj_eq_self_iff E _).mp (by
      simp only [map_div₀, map_sub, map_mul, map_ofNat,
        IsCMField.complexConj_apply_apply, hδ, mul_neg]
      rw [← neg_sub, neg_div_neg_eq])⟩

lemma coordinate_decomposition (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (x : E) :
    (realCoordinate x : E) + (imaginaryCoordinate δ hδ x : E) * δ = x := by
  change (x + IsCMField.complexConj E x) / 2 +
    ((x - IsCMField.complexConj E x) / (2 * δ)) * δ = x
  field_simp
  ring

def quadraticLift (δ : E) (hδ : IsCMField.complexConj E δ = -δ) :
    QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0 →ₐ[RealField E] E :=
  QuadraticAlgebra.lift ⟨δ, by
    simp only [Algebra.smul_def, map_zero, zero_mul, add_zero, mul_one]
    change δ * δ = δ ^ 2
    exact (pow_two δ).symm⟩

lemma quadraticLift_apply (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (z : QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0) :
    quadraticLift δ hδ z = (z.re : E) + (z.im : E) * δ := by
  simp [quadraticLift, QuadraticAlgebra.lift, Algebra.smul_def]
  rfl

lemma quadraticLift_conjugate (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (z : QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0) :
    IsCMField.complexConj E (quadraticLift δ hδ z) = (z.re : E) - (z.im : E) * δ := by
  simp [quadraticLift_apply, map_add, map_mul,
    IsCMField.complexConj_apply_eq_self, hδ, sub_eq_add_neg]

lemma realCoordinate_quadraticLift (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (z : QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0) :
    realCoordinate (quadraticLift δ hδ z) = z.re := by
  apply Subtype.ext
  change (quadraticLift δ hδ z + IsCMField.complexConj E (quadraticLift δ hδ z)) / 2 = _
  rw [quadraticLift_conjugate, quadraticLift_apply]
  field_simp
  ring

lemma imaginaryCoordinate_quadraticLift (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (z : QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0) :
    imaginaryCoordinate δ hδ (quadraticLift δ hδ z) = z.im := by
  apply Subtype.ext
  change (quadraticLift δ hδ z - IsCMField.complexConj E (quadraticLift δ hδ z)) / (2 * δ) = _
  rw [quadraticLift_conjugate, quadraticLift_apply]
  field_simp
  ring

/-- The quadratic algebra is the actual CM field, not an assumed model. -/
def quadraticEquiv (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    QuadraticAlgebra (RealField E) (imaginarySquare δ hδ) 0 ≃ₐ[RealField E] E :=
  AlgEquiv.ofBijective (quadraticLift δ hδ) ⟨by
    intro z w h
    apply QuadraticAlgebra.ext
    · have hh := congrArg realCoordinate h
      simpa only [realCoordinate_quadraticLift] using hh
    · have hh := congrArg (imaginaryCoordinate δ hδ) h
      simpa only [imaginaryCoordinate_quadraticLift δ hδ hδ0] using hh,
    by
      intro x
      refine ⟨⟨realCoordinate x, imaginaryCoordinate δ hδ x⟩, ?_⟩
      exact (quadraticLift_apply _ _ _).trans (coordinate_decomposition δ hδ hδ0 x)⟩

lemma imaginary_generator_embedding_re (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (μ : E →+* ℂ) : (μ δ).re = 0 := by
  have h := congrArg (fun x : E => (μ x).re) hδ
  rw [IsCMField.complexEmbedding_complexConj, map_neg] at h
  change (μ δ).re = -(μ δ).re at h
  linarith

lemma imaginary_square_negative (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (μ : E →+* ℂ) : (μ (imaginarySquare δ hδ : E)).re < 0 := by
  have hμ0 : μ δ ≠ 0 := (map_ne_zero μ).mpr hδ0
  have hre := imaginary_generator_embedding_re δ hδ μ
  have him : (μ δ).im ≠ 0 := by
    intro h
    apply hμ0
    exact Complex.ext hre h
  change (μ (δ ^ 2)).re < 0
  rw [map_pow]
  simp only [pow_two, Complex.mul_re, hre, zero_mul, zero_sub]
  exact neg_neg_of_pos (mul_self_pos.mpr him)

end

section

/-! Explicit six-dimensional restriction of scalars for a rank-three module
over K[δ]/(δ²-d). Entries are polynomial in d and in the two coordinates of
each original matrix entry. -/

open scoped BigOperators Classical QuadraticAlgebra

section Ring
variable {K : Type*} [CommRing K]

def quadraticRegular (d : K) : QuadraticAlgebra K d 0 →+* Matrix (Fin 2) (Fin 2) K where
  toFun z := !![z.re, d * z.im; z.im, z.re]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

abbrev pairIndex : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv

/-- The faithful regular matrix representation over K. -/
def regularMatrix (d : K) :
    Mat (QuadraticAlgebra K d 0) →+* Matrix (Fin 6) (Fin 6) K :=
  (Matrix.reindexRingEquiv K pairIndex).toRingHom.comp
    ((Matrix.compRingEquiv (Fin 3) (Fin 2) K).toRingHom.comp
      (quadraticRegular d).mapMatrix)

lemma regularMatrix_entry (d : K) (A : Mat (QuadraticAlgebra K d 0))
    (i j : Fin 3) (a b : Fin 2) :
    regularMatrix d A (pairIndex (i, a)) (pairIndex (j, b)) =
      quadraticRegular d (A i j) a b := by
  simp [regularMatrix, Matrix.reindex_apply, Matrix.comp_apply]

/-- The first column of each 2 by 2 block recovers its quadratic entry. -/
def decodeMatrix (d : K) (M : Matrix (Fin 6) (Fin 6) K) : Mat (QuadraticAlgebra K d 0) :=
  fun i j => ⟨M (pairIndex (i, 0)) (pairIndex (j, 0)),
    M (pairIndex (i, 1)) (pairIndex (j, 0))⟩

@[simp] lemma decode_regularMatrix (d : K) (A : Mat (QuadraticAlgebra K d 0)) :
    decodeMatrix d (regularMatrix d A) = A := by
  apply Matrix.ext
  intro i j
  apply QuadraticAlgebra.ext
  · simp [decodeMatrix, regularMatrix_entry, quadraticRegular]
  · simp [decodeMatrix, regularMatrix_entry, quadraticRegular]

theorem regularMatrix_injective (d : K) : Function.Injective (regularMatrix d) :=
  Function.LeftInverse.injective (decode_regularMatrix d)

end Ring

variable {K L : Type*} [CommRing K] [CommRing L]

def quadraticMap (d : K) (f : K →+* L) :
    QuadraticAlgebra K d 0 →+* QuadraticAlgebra L (f d) 0 where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp [map_add, map_mul]

lemma quadraticRegular_map (d : K) (f : K →+* L) (z : QuadraticAlgebra K d 0) :
    quadraticRegular (f d) (quadraticMap d f z) = (quadraticRegular d z).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadraticRegular, quadraticMap, map_mul]

theorem regularMatrix_map (d : K) (f : K →+* L) (A : Mat (QuadraticAlgebra K d 0)) :
    regularMatrix (f d) (A.map (quadraticMap d f)) = (regularMatrix d A).map f := by
  apply Matrix.ext
  intro i j
  obtain ⟨⟨i, a⟩, rfl⟩ := pairIndex.surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := pairIndex.surjective j
  simp only [regularMatrix_entry, Matrix.map_apply]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M a b) (quadraticRegular_map d f (A i j))

end

section

/-! The explicit regular matrices are the matrices of restriction of scalars
in a specified basis. In particular their determinant is the quadratic norm
of the original determinant, so determinant-one matrices map into SL(6). -/

open scoped BigOperators Classical QuadraticAlgebra

variable {K : Type*} [CommRing K]

def quadraticCoordinates (d : K) :
    Vec (QuadraticAlgebra K d 0) ≃ₗ[K] (Fin 6 → K) where
  toFun x i := if (pairIndex.symm i).2 = 0 then (x (pairIndex.symm i).1).re
    else (x (pairIndex.symm i).1).im
  invFun y i := ⟨y (pairIndex (i, 0)), y (pairIndex (i, 1))⟩
  left_inv x := by ext i <;> simp
  right_inv y := by
    ext i
    obtain ⟨⟨i, a⟩, rfl⟩ := pairIndex.surjective i
    fin_cases a <;> simp
  map_add' x y := by
    ext i
    split_ifs <;> simp_all
  map_smul' a x := by
    ext i
    split_ifs <;> simp_all

lemma quadraticCoordinates_pair (d : K) (x : Vec (QuadraticAlgebra K d 0))
    (i : Fin 3) (a : Fin 2) :
    quadraticCoordinates d x (pairIndex (i, a)) =
      if a = 0 then (x i).re else (x i).im := by
  simp [quadraticCoordinates]

def restrictionBasis (d : K) : Module.Basis (Fin 6) K (Vec (QuadraticAlgebra K d 0)) :=
  Module.Basis.ofEquivFun (quadraticCoordinates d)

theorem quadraticCoordinates_mulVec (d : K) (A : Mat (QuadraticAlgebra K d 0))
    (x : Vec (QuadraticAlgebra K d 0)) :
    quadraticCoordinates d (A.mulVec x) =
      (regularMatrix d A).mulVec (quadraticCoordinates d x) := by
  ext r
  obtain ⟨⟨i, a⟩, rfl⟩ := pairIndex.surjective r
  change _ = ∑ j : Fin 6, regularMatrix d A (pairIndex (i, a)) j * quadraticCoordinates d x j
  rw [← Equiv.sum_comp pairIndex]
  rw [Fintype.sum_prod_type]
  simp only [regularMatrix_entry, quadraticCoordinates_pair]
  fin_cases a
  · simp [quadraticRegular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [quadraticRegular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

theorem regularMatrix_eq_restriction (d : K) (A : Mat (QuadraticAlgebra K d 0)) :
    regularMatrix d A = LinearMap.toMatrix (restrictionBasis d) (restrictionBasis d)
      ((Matrix.toLin' A).restrictScalars K) := by
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply]
  simp only [restrictionBasis, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
  change regularMatrix d A i j =
    quadraticCoordinates d (A.mulVec ((quadraticCoordinates d).symm (Pi.single j 1))) i
  rw [quadraticCoordinates_mulVec, LinearEquiv.apply_symm_apply]
  simp [Matrix.mulVec_single]

theorem regularMatrix_det (d : K) (A : Mat (QuadraticAlgebra K d 0)) :
    (regularMatrix d A).det = Algebra.norm K A.det := by
  rw [regularMatrix_eq_restriction, LinearMap.det_toMatrix, LinearMap.det_restrictScalars,
    LinearMap.det_toLin']

def regularSpecialLinear (d : K) :
    SL (QuadraticAlgebra K d 0) →* Matrix.SpecialLinearGroup (Fin 6) K where
  toFun g := ⟨regularMatrix d (g : Mat (QuadraticAlgebra K d 0)), by
    rw [regularMatrix_det, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one (regularMatrix d))
  map_mul' g h := Subtype.ext (map_mul (regularMatrix d) _ _)

theorem regularSpecialLinear_injective (d : K) :
    Function.Injective (regularSpecialLinear d) := by
  intro g h he
  apply Subtype.ext
  exact regularMatrix_injective d (congrArg Subtype.val he)

end

section

/-! The actual special unitary group as a subgroup of SL(6), with explicit
finite equations characterizing its image. These equations consist of block
shape, the quadratic-valued determinant, and Hermitian column pairings. -/

open scoped BigOperators Classical QuadraticAlgebra

section Ring
variable {K : Type*} [CommRing K]

def columnError (d b : K) (A : Mat (QuadraticAlgebra K d 0)) :
    Mat (QuadraticAlgebra K d 0) := fun i j =>
  (∑ k, diagonalCoefficient (algebraMap K _ b) k * A k i * star (A k j)) -
    if i = j then diagonalCoefficient (algebraMap K _ b) i else 0

lemma columnError_eq_zero_iff (d b : K) (A : SL (QuadraticAlgebra K d 0)) :
    columnError d b (A : Mat (QuadraticAlgebra K d 0)) = 0 ↔
      A ∈ unitarySubgroup (starRingEnd _) (algebraMap K _ b) := by
  rw [unitary_iff_columns]
  constructor
  · intro h i j
    have hij := congrArg (fun M : Mat (QuadraticAlgebra K d 0) => M i j) h
    exact sub_eq_zero.mp hij
  · intro h
    apply Matrix.ext
    intro i j
    exact sub_eq_zero.mpr (h i j)

/-- The faithful six-dimensional special unitary group over K. -/
def sixDimensionalUnitary (d b : K) : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K) :=
  (unitarySubgroup (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b)).map
    (regularSpecialLinear d)

/-- Explicit equations characterize membership, with no realization assumed. -/
theorem mem_sixDimensionalUnitary_iff (d b : K) (M : Matrix.SpecialLinearGroup (Fin 6) K) :
    M ∈ sixDimensionalUnitary d b ↔
      regularMatrix d (decodeMatrix d M.val) = M.val ∧
      (decodeMatrix d M.val).det = 1 ∧
      columnError d b (decodeMatrix d M.val) = 0 := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    change regularMatrix d (decodeMatrix d (regularMatrix d A.val)) = regularMatrix d A.val ∧
      (decodeMatrix d (regularMatrix d A.val)).det = 1 ∧
      columnError d b (decodeMatrix d (regularMatrix d A.val)) = 0
    rw [decode_regularMatrix]
    exact ⟨rfl, A.property, (columnError_eq_zero_iff d b A).mpr hA⟩
  · rintro ⟨hshape, hdet, hform⟩
    let A : SL (QuadraticAlgebra K d 0) := ⟨decodeMatrix d M.val, hdet⟩
    exact ⟨A, (columnError_eq_zero_iff d b A).mp hform, Subtype.ext hshape⟩

end Ring

variable {K L : Type*} [CommRing K] [CommRing L]

lemma quadraticMap_star (d : K) (f : K →+* L) (z : QuadraticAlgebra K d 0) :
    quadraticMap d f (star z) = star (quadraticMap d f z) := by
  apply QuadraticAlgebra.ext <;> simp [quadraticMap, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star]

lemma quadraticMap_algebraMap (d b : K) (f : K →+* L) :
    quadraticMap d f (algebraMap K (QuadraticAlgebra K d 0) b) =
      algebraMap L (QuadraticAlgebra L (f d) 0) (f b) := by
  apply QuadraticAlgebra.ext <;> simp [quadraticMap]

lemma columnError_map (d b : K) (f : K →+* L) (A : Mat (QuadraticAlgebra K d 0)) :
    (columnError d b A).map (quadraticMap d f) =
      columnError (f d) (f b) (A.map (quadraticMap d f)) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, columnError, map_sub, map_sum, map_mul,
    diagonalCoefficient, apply_ite, map_one, map_zero,
    quadraticMap_algebraMap, quadraticMap_star]
  split_ifs <;> simp_all

lemma decodeMatrix_map (d : K) (f : K →+* L) (M : Matrix (Fin 6) (Fin 6) K) :
    (decodeMatrix d M).map (quadraticMap d f) = decodeMatrix (f d) (M.map f) := rfl

end

/-! Actual ground-field polynomials cutting out the six-dimensional unitary
group. Evaluation of this fixed family recovers its matrix equations over
every scalar extension. -/

open scoped BigOperators Classical QuadraticAlgebra

abbrev EquationIndex := (Fin 6 × Fin 6) ⊕ (Fin 2 ⊕ ((Fin 3 × Fin 3) × Fin 2))

def quadraticComponent {K : Type*} [Zero K] {d : K}
    (a : Fin 2) (z : QuadraticAlgebra K d (0 : K)) : K := if a = 0 then z.re else z.im

section Ring
variable {K : Type*} [CommRing K]

def unitaryEquation (d b : K) (M : Matrix (Fin 6) (Fin 6) K) : EquationIndex → K
  | .inl (i, j) => M i j - regularMatrix d (decodeMatrix d M) i j
  | .inr (.inl a) => quadraticComponent a ((decodeMatrix d M).det - 1)
  | .inr (.inr ((i, j), a)) => quadraticComponent a (columnError d b (decodeMatrix d M) i j)

theorem unitaryEquation_zero_iff (d b : K) (M : Matrix.SpecialLinearGroup (Fin 6) K) :
    (∀ e : EquationIndex, unitaryEquation d b M.val e = 0) ↔
      M ∈ sixDimensionalUnitary d b := by
  rw [mem_sixDimensionalUnitary_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply Matrix.ext
      intro i j
      exact (sub_eq_zero.mp (h (.inl (i, j)))).symm
    · apply sub_eq_zero.mp
      apply QuadraticAlgebra.ext
      · exact h (.inr (.inl 0))
      · exact h (.inr (.inl 1))
    · apply Matrix.ext
      intro i j
      apply QuadraticAlgebra.ext
      · exact h (.inr (.inr ((i, j), 0)))
      · exact h (.inr (.inr ((i, j), 1)))
  · rintro ⟨hshape, hdet, hcol⟩ e
    rcases e with ⟨i, j⟩ | (a | ⟨⟨i, j⟩, a⟩) <;>
      simp [unitaryEquation, hshape, hdet, hcol, quadraticComponent]

end Ring

section ScalarExtension
variable {K L : Type*} [CommRing K] [CommRing L]

lemma quadraticComponent_map (d : K) (f : K →+* L) (a : Fin 2)
    (z : QuadraticAlgebra K d 0) :
    f (quadraticComponent a z) = quadraticComponent a (quadraticMap d f z) := by
  fin_cases a <;> simp [quadraticComponent, quadraticMap]

lemma decode_determinant_map (d : K) (f : K →+* L) (M : Matrix (Fin 6) (Fin 6) K) :
    quadraticMap d f ((decodeMatrix d M).det - 1) =
      (decodeMatrix (f d) (M.map f)).det - 1 := by
  rw [map_sub, map_one, RingHom.map_det, RingHom.mapMatrix_apply, decodeMatrix_map]

lemma unitaryEquation_map (d b : K) (f : K →+* L) (M : Matrix (Fin 6) (Fin 6) K)
    (e : EquationIndex) :
    f (unitaryEquation d b M e) = unitaryEquation (f d) (f b) (M.map f) e := by
  rcases e with ⟨i, j⟩ | (a | ⟨⟨i, j⟩, a⟩)
  · have h := regularMatrix_map d f (decodeMatrix d M)
    rw [decodeMatrix_map] at h
    change f (M i j - regularMatrix d (decodeMatrix d M) i j) =
      f (M i j) - regularMatrix (f d) (decodeMatrix (f d) (M.map f)) i j
    rw [map_sub, h]
    rfl
  · change f (quadraticComponent a ((decodeMatrix d M).det - 1)) = _
    rw [quadraticComponent_map, decode_determinant_map]
    rfl
  · have h := columnError_map d b f (decodeMatrix d M)
    rw [decodeMatrix_map] at h
    change f (quadraticComponent a (columnError d b (decodeMatrix d M) i j)) = _
    rw [quadraticComponent_map]
    exact congrArg (fun A : Mat (QuadraticAlgebra L (f d) 0) => quadraticComponent a (A i j)) h

end ScalarExtension

abbrev GroundPolynomial (K : Type*) [CommRing K] := MvPolynomial (Fin 6 × Fin 6) K

def variableMatrix (K : Type*) [CommRing K] : Matrix (Fin 6) (Fin 6) (GroundPolynomial K) :=
  fun i j => MvPolynomial.X (i, j)

def unitaryPolynomial {K : Type*} [CommRing K] (d b : K) (e : EquationIndex) : GroundPolynomial K :=
  unitaryEquation (MvPolynomial.C d) (MvPolynomial.C b) (variableMatrix K) e

theorem unitaryPolynomial_eval {K L : Type*} [CommRing K] [CommRing L]
    (d b : K) (f : K →+* L) (M : Matrix (Fin 6) (Fin 6) L) (e : EquationIndex) :
    MvPolynomial.eval₂Hom f (fun ij => M ij.1 ij.2) (unitaryPolynomial d b e) =
      unitaryEquation (f d) (f b) M e := by
  let φ : GroundPolynomial K →+* L := MvPolynomial.eval₂Hom f (fun ij => M ij.1 ij.2)
  have hM : (variableMatrix K).map φ = M := by
    ext i j
    simp [variableMatrix, φ]
  change φ (unitaryEquation (MvPolynomial.C d) (MvPolynomial.C b) (variableMatrix K) e) = _
  rw [unitaryEquation_map, hM]
  simp only [φ, MvPolynomial.eval₂Hom_C]

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
