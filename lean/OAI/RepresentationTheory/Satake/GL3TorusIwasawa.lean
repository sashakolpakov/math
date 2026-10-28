import Mathlib

/-! # GL 3 Torus Iwasawa -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa

/-!
The constant-term map on the actual finite-support spherical convolution
algebra. The only decomposition inputs are G = BK and a homomorphism from
B to the lattice that kills B ∩ K. These are group-theoretic inputs, not
multiplicativity, injectivity, Weyl invariance, or a Satake isomorphism.

For a split reductive local group, B is the chosen Borel, and the lattice
map is the valuation of its torus quotient. Establishing those geometric
inputs and the Weyl-invariant image remains separate from this construction.
-/

open scoped Classical

variable {G L : Type*} [Group G] [AddCommGroup L]

/-- The complex permutation module of right K-cosets. -/
abbrev CosetModule (K : Subgroup G) := (G ⧸ K) →₀ ℂ

def regular (K : Subgroup G) (g : G) : Module.End ℂ (CosetModule K) :=
  Finsupp.lmapDomain ℂ ℂ (fun x : G ⧸ K => g • x)

/-- Equivariant endomorphisms, with multiplication given by composition. -/
def algebra (K : Subgroup G) : Subalgebra ℂ (Module.End ℂ (CosetModule K)) :=
  Subalgebra.centralizer ℂ (Set.range (regular K))

def delta (K : Subgroup G) : CosetModule K :=
  Finsupp.single (QuotientGroup.mk (1 : G)) 1

def kernel (K : Subgroup G) (T : algebra K) : CosetModule K := T.val (delta K)

theorem regular_delta (K : Subgroup G) (g : G) :
    regular K g (delta K) = Finsupp.single (QuotientGroup.mk g) 1 := by
  simp [regular, delta]

theorem regular_mul (K : Subgroup G) (g h : G) :
    regular K (g * h) = regular K g * regular K h := by
  apply Finsupp.lhom_ext
  intro x c
  simp [regular, Module.End.mul_apply, mul_smul]

/-- Evaluation at the identity coset determines an equivariant operator. -/
theorem kernel_injective (K : Subgroup G) : Function.Injective (kernel K) := by
  intro T U hkernel
  apply Subtype.ext
  apply Finsupp.lhom_ext
  intro x c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hT := T.property (regular K g) ⟨g, rfl⟩
  have hU := U.property (regular K g) ⟨g, rfl⟩
  have hbase : T.val (Finsupp.single (QuotientGroup.mk g) 1) =
      U.val (Finsupp.single (QuotientGroup.mk g) 1) := by
    rw [← regular_delta]
    change (T.val * regular K g) (delta K) = (U.val * regular K g) (delta K)
    rw [← hT, ← hU]
    exact congrArg (regular K g) hkernel
  have hscaled := congrArg (fun v : CosetModule K => c • v) hbase
  simpa only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hscaled

/-- An Iwasawa decomposition and its torus valuation. -/
structure Decomposition (K : Subgroup G) (L : Type*) [AddCommGroup L] where
  B : Subgroup G
  valuation : B →* Multiplicative L
  compact_valuation : ∀ b : B, (b : G) ∈ K → valuation b = 1
  factorization : ∀ g : G, ∃ b : B, ∃ k : K, g = (b : G) * (k : G)

namespace Decomposition

variable {K : Subgroup G} (D : Decomposition K L)

theorem exists_representative (x : G ⧸ K) :
    ∃ b : D.B, QuotientGroup.mk (b : G) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, k, rfl⟩ := D.factorization g
  refine ⟨b, QuotientGroup.eq.mpr ?_⟩
  simpa only [inv_mul_cancel_left] using k.property

def representative (x : G ⧸ K) : D.B :=
  (D.exists_representative x).choose

theorem representative_spec (x : G ⧸ K) :
    QuotientGroup.mk (D.representative x : G) = x :=
  (D.exists_representative x).choose_spec

theorem valuation_eq_of_same_coset (b c : D.B)
    (h : (QuotientGroup.mk (b : G) : G ⧸ K) = QuotientGroup.mk (c : G)) :
    D.valuation b = D.valuation c := by
  have hbc : ((b⁻¹ * c : D.B) : G) ∈ K := QuotientGroup.eq.mp h
  have hv := D.compact_valuation (b⁻¹ * c) hbc
  simpa only [map_mul, map_inv, inv_mul_eq_one] using hv

/-- The torus valuation of a right K-coset. -/
def height (x : G ⧸ K) : L := (D.valuation (D.representative x)).toAdd

@[simp]
theorem height_mk (b : D.B) :
    D.height (QuotientGroup.mk (b : G)) = (D.valuation b).toAdd := by
  exact congrArg Multiplicative.toAdd
    (D.valuation_eq_of_same_coset _ b (D.representative_spec _))

@[simp]
theorem height_one : D.height (QuotientGroup.mk (1 : G)) = 0 := by
  simpa using D.height_mk (1 : D.B)

theorem height_smul (b : D.B) (x : G ⧸ K) :
    D.height ((b : G) • x) = (D.valuation b).toAdd + D.height x := by
  have hx : (b : G) • x = QuotientGroup.mk ((b * D.representative x : D.B) : G) := by
    calc
      (b : G) • x = (b : G) • QuotientGroup.mk (D.representative x : G) :=
        congrArg (fun y : G ⧸ K => (b : G) • y) (D.representative_spec x).symm
      _ = _ := rfl
  rw [hx, D.height_mk, map_mul]
  rfl

/-- Push finite-support functions along the actual Iwasawa height. -/
def pushforward : CosetModule K →ₗ[ℂ] AddMonoidAlgebra ℂ L :=
  Finsupp.linearCombination ℂ fun x => AddMonoidAlgebra.single (D.height x) 1

@[simp]
theorem pushforward_single (x : G ⧸ K) (c : ℂ) :
    D.pushforward (Finsupp.single x c) = AddMonoidAlgebra.single (D.height x) c := by
  simp [Decomposition.pushforward]

theorem pushforward_coeff (v : CosetModule K) :
    (D.pushforward v).coeff = Finsupp.mapDomain D.height v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, Finsupp.mapDomain_add]
  | single x c => simp

@[simp]
theorem regular_single (g : G) (x : G ⧸ K) (c : ℂ) :
    regular K g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [regular]

theorem pushforward_regular (b : D.B) (v : CosetModule K) :
    D.pushforward (regular K (b : G) v) =
      AddMonoidAlgebra.single (D.valuation b).toAdd 1 * D.pushforward v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]
  | single x c => simp [D.height_smul, AddMonoidAlgebra.single_mul_single]

/-- The convolution-kernel map is linear; its value at the identity
operator is the delta function of K. -/
def kernelLinear : algebra K →ₗ[ℂ] CosetModule K where
  toFun := kernel K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The unnormalized constant term, defined by a finite pushforward. -/
def constantTermLinear : algebra K →ₗ[ℂ] AddMonoidAlgebra ℂ L :=
  D.pushforward.comp kernelLinear

theorem pushforward_hecke (T : algebra K) (v : CosetModule K) :
    D.pushforward (T.val v) = D.constantTermLinear T * D.pushforward v := by
  have hsingle (x : G ⧸ K) :
      D.pushforward (T.val (Finsupp.single x 1)) =
        D.constantTermLinear T * AddMonoidAlgebra.single (D.height x) 1 := by
    let b := D.representative x
    have hx : Finsupp.single x 1 = regular K (b : G) (delta K) := by
      rw [regular_delta, D.representative_spec]
    have hT := T.property (regular K (b : G)) ⟨b, rfl⟩
    rw [hx]
    change D.pushforward ((T.val * regular K (b : G)) (delta K)) = _
    rw [← hT]
    change D.pushforward (regular K (b : G) (kernel K T)) = _
    rw [D.pushforward_regular]
    exact mul_comm _ _
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]
  | single x c =>
    have hx : Finsupp.single x c = c • Finsupp.single x 1 := by simp
    rw [hx, map_smul, map_smul, hsingle, map_smul, D.pushforward_single]
    exact (mul_smul_comm c (D.constantTermLinear T)
      (AddMonoidAlgebra.single (D.height x) 1)).symm

@[simp]
theorem constantTerm_one : D.constantTermLinear 1 = 1 := by
  change D.pushforward (delta K) = 1
  simp [delta, AddMonoidAlgebra.one_def]

theorem constantTerm_mul (T U : algebra K) :
    D.constantTermLinear (T * U) = D.constantTermLinear T * D.constantTermLinear U :=
  D.pushforward_hecke T (kernel K U)

/-- Multiplicativity of the actual constant term follows from equivariance. -/
def constantTerm : algebra K →ₐ[ℂ] AddMonoidAlgebra ℂ L where
  toFun := D.constantTermLinear
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := D.constantTerm_one
  map_mul' := D.constantTerm_mul
  commutes' c := by
    change D.constantTermLinear (c • (1 : algebra K)) = _
    rw [map_smul, D.constantTerm_one]
    exact Algebra.smul_def c 1 |>.trans (mul_one _)

end Decomposition

end RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa

namespace RepresentationTheory.Satake.GL3TorusIwasawa.Normalization

/-!
Modulus normalization for the finite-support Satake transform. Multiplying
each lattice monomial by a group character is an algebra automorphism.
The conventional normalization is built from the positive square root of
the residue-field cardinality and the sum of the positive roots.
-/

variable {L : Type*} [AddCommGroup L]

def weightedMonomial (χ : Multiplicative L →* ℂˣ) :
    Multiplicative L →* AddMonoidAlgebra ℂ L :=
  ((algebraMap ℂ (AddMonoidAlgebra ℂ L)).toMonoidHom.comp
    ((Units.coeHom ℂ).comp χ)) * AddMonoidAlgebra.of ℂ L

/-- Multiply each monomial by its value under the normalizing character. -/
def twist (χ : Multiplicative L →* ℂˣ) :
    AddMonoidAlgebra ℂ L →ₐ[ℂ] AddMonoidAlgebra ℂ L :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ L) L (weightedMonomial χ)

@[simp]
theorem twist_single (χ : Multiplicative L →* ℂˣ) (ell : L) (c : ℂ) :
    twist χ (AddMonoidAlgebra.single ell c) =
      AddMonoidAlgebra.single ell (c * (χ (Multiplicative.ofAdd ell) : ℂ)) := by
  simp [twist, weightedMonomial, Algebra.smul_def, AddMonoidAlgebra.single_mul_single]

theorem twist_coeff (χ : Multiplicative L →* ℂˣ)
    (f : AddMonoidAlgebra ℂ L) (ell : L) :
    (twist χ f).coeff ell = f.coeff ell * (χ (Multiplicative.ofAdd ell) : ℂ) := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul]
  | single a c =>
    by_cases h : a = ell
    · subst a; simp
    · simp [h]

/-- The normalizing character can be inverted, so normalization loses no information. -/
def twistEquiv (χ : Multiplicative L →* ℂˣ) :
    AddMonoidAlgebra ℂ L ≃ₐ[ℂ] AddMonoidAlgebra ℂ L :=
  AlgEquiv.ofAlgHom (twist χ) (twist χ⁻¹)
    (by ext ell; simp)
    (by ext ell; simp)

def residueSqrtUnit (q : ℕ) (hq : 0 < q) : ℂˣ :=
  Units.mk0 (Real.sqrt (q : ℝ) : ℂ) (by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < q by exact_mod_cast hq)).ne')

/-- If `twoRho` is the sum of positive roots, this character is
q^(-⟨ρ,ell⟩), with the positive real square root used when needed. -/
def modulusWeight (q : ℕ) (hq : 0 < q) (twoRho : L →+ ℤ) :
    Multiplicative L →* ℂˣ where
  toFun ell := residueSqrtUnit q hq ^ (-twoRho ell.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change residueSqrtUnit q hq ^ (-twoRho (a.toAdd + b.toAdd)) = _
    rw [map_add, neg_add, zpow_add]

/-- The actual normalized transform: first push the Hecke kernel along
Iwasawa height, then apply the modulus character. -/
def satake {G : Type*} [Group G] {K : Subgroup G}
    (D : Iwasawa.Decomposition K L)
    (q : ℕ) (hq : 0 < q) (twoRho : L →+ ℤ) :
    Iwasawa.algebra K →ₐ[ℂ] AddMonoidAlgebra ℂ L :=
  (twist (modulusWeight q hq twoRho)).comp D.constantTerm

theorem satake_coeff {G : Type*} [Group G] {K : Subgroup G}
    (D : Iwasawa.Decomposition K L)
    (q : ℕ) (hq : 0 < q) (twoRho : L →+ ℤ)
    (T : Iwasawa.algebra K) (ell : L) :
    (satake D q hq twoRho T).coeff ell =
      (D.constantTerm T).coeff ell *
        (Real.sqrt (q : ℝ) : ℂ) ^ (-twoRho ell) := by
  rw [satake, AlgHom.comp_apply, twist_coeff]
  simp [modulusWeight, residueSqrtUnit]

end RepresentationTheory.Satake.GL3TorusIwasawa.Normalization

namespace RepresentationTheory.Satake.GL3TorusIwasawa.Torus

/-!
The torus case of Satake, proved for an abelian group whose quotient by K
is its valuation lattice. The spherical algebra remains the actual
equivariant endomorphism algebra; it is not defined as the lattice algebra.
The proof constructs all monomials as translation kernels and proves
injectivity using the bijective valuation map on cosets.
-/

open OAI.RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa

variable {G L : Type*} [CommGroup G] [AddCommGroup L]

/-- For an abelian group the regular translations themselves are spherical. -/
def translation (K : Subgroup G) (g : G) : Iwasawa.algebra K :=
  ⟨Iwasawa.regular K g, by
    rintro _ ⟨h, rfl⟩
    rw [← Iwasawa.regular_mul, ← Iwasawa.regular_mul, mul_comm]⟩

def decomposition (ν : G →* Multiplicative L) : Iwasawa.Decomposition ν.ker L where
  B := ⊤
  valuation := ν.comp (⊤ : Subgroup G).subtype
  compact_valuation b hb := hb
  factorization g := ⟨⟨g, Subgroup.mem_top g⟩, 1, by simp⟩

@[simp]
theorem height_mk (ν : G →* Multiplicative L) (g : G) :
    (decomposition ν).height (QuotientGroup.mk g) = (ν g).toAdd :=
  (decomposition ν).height_mk ⟨g, Subgroup.mem_top g⟩

theorem height_injective (ν : G →* Multiplicative L) :
    Function.Injective (decomposition ν).height := by
  intro x y h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Torus.height_mk, Torus.height_mk] at h
  have hν : ν g = ν u := Multiplicative.toAdd.injective h
  apply QuotientGroup.eq.mpr
  change ν (g⁻¹ * u) = 1
  simp [hν]

@[simp]
theorem constantTerm_translation (ν : G →* Multiplicative L) (g : G) :
    (decomposition ν).constantTerm (translation ν.ker g) =
      AddMonoidAlgebra.single (ν g).toAdd 1 := by
  change (decomposition ν).pushforward (Iwasawa.regular ν.ker g (Iwasawa.delta ν.ker)) = _
  rw [Iwasawa.regular_delta, Iwasawa.Decomposition.pushforward_single, Torus.height_mk]

theorem constantTerm_injective (ν : G →* Multiplicative L) :
    Function.Injective (decomposition ν).constantTerm := by
  intro T U h
  apply Iwasawa.kernel_injective ν.ker
  apply Finsupp.mapDomain_injective (height_injective ν)
  have hcoeff := congrArg AddMonoidAlgebra.coeff h
  change ((decomposition ν).pushforward (Iwasawa.kernel ν.ker T)).coeff =
    ((decomposition ν).pushforward (Iwasawa.kernel ν.ker U)).coeff at hcoeff
  simpa only [Iwasawa.Decomposition.pushforward_coeff] using hcoeff

theorem constantTerm_surjective (ν : G →* Multiplicative L)
    (hν : Function.Surjective ν) :
    Function.Surjective (decomposition ν).constantTerm := by
  intro f
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨T, rfl⟩ := hf
    obtain ⟨U, rfl⟩ := hg
    exact ⟨T + U, map_add _ T U⟩
  | single ell c =>
    obtain ⟨g, hg⟩ := hν (Multiplicative.ofAdd ell)
    refine ⟨c • translation ν.ker g, ?_⟩
    simp [hg]

/-- The genuine spherical convolution algebra of an abelian group with
valuation lattice L is its complex group algebra. -/
def satakeEquiv (ν : G →* Multiplicative L) (hν : Function.Surjective ν) :
    Iwasawa.algebra ν.ker ≃ₐ[ℂ] AddMonoidAlgebra ℂ L :=
  AlgEquiv.ofBijective (decomposition ν).constantTerm
    ⟨constantTerm_injective ν, constantTerm_surjective ν hν⟩

end RepresentationTheory.Satake.GL3TorusIwasawa.Torus

namespace RepresentationTheory.Satake.GL3TorusIwasawa.LocalTorus

/-!
The concrete split-torus case over a nonarchimedean local field. The group
is (Fˣ)^r, the compact level consists of units of the valuation ring in
each coordinate, and the cocharacter lattice is ℤ^r. The integer valuation
is constructed from Mathlib's proved discrete value-group classification.
-/

open ValuativeRel

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

def valueUnits : Fˣ →* (ValueGroupWithZero F)ˣ :=
  Units.map (valuation F).toMonoidWithZeroHom.toMonoidHom

def integerValueEquiv : (ValueGroupWithZero F)ˣ ≃* Multiplicative ℤ :=
  (Units.mapEquiv (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMulEquiv).trans
    WithZero.unitsWithZeroEquiv

/-- Additive valuation, with uniformizers having positive exponent. -/
def exponent : Fˣ →* Multiplicative ℤ :=
  ((integerValueEquiv F).toMonoidHom.comp (valueUnits F))⁻¹

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem valueUnits_surjective : Function.Surjective (valueUnits F) := by
  intro a
  obtain ⟨x, hx⟩ := valuation_surjective (a : ValueGroupWithZero F)
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    have ha : (a : ValueGroupWithZero F) = 0 := by simpa using hx.symm
    exact a.ne_zero ha
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact hx

theorem exponent_surjective : Function.Surjective (exponent F) := by
  intro a
  obtain ⟨x, hx⟩ := valueUnits_surjective F ((integerValueEquiv F).symm a⁻¹)
  refine ⟨x, ?_⟩
  simp [exponent, hx]

theorem exponent_eq_one_iff (x : Fˣ) :
    exponent F x = 1 ↔ valuation F (x : F) = 1 := by
  change ((integerValueEquiv F) (valueUnits F x))⁻¹ = 1 ↔ _
  rw [inv_eq_one, (integerValueEquiv F).map_eq_one_iff]
  exact Units.ext_iff

/-- The actual integral-unit subgroup, realized by the inclusion O_F → F. -/
def integralUnits : Subgroup Fˣ :=
  (Units.map (valuation F).integer.subtype.toMonoidHom).range

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_integralUnits_iff (x : Fˣ) :
    x ∈ integralUnits F ↔ valuation F (x : F) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation F))).mp u.isUnit
  · intro hx
    let r : (valuation F).integer := ⟨(x : F), hx.le⟩
    have hr : IsUnit r := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation F))).mpr hx
    refine ⟨hr.unit, ?_⟩
    apply Units.ext
    change ((hr.unit : (valuation F).integer) : F) = (x : F)
    rw [hr.unit_spec]

def latticeValuation (r : ℕ) :
    (Fin r → Fˣ) →* Multiplicative (Fin r → ℤ) where
  toFun x := Multiplicative.ofAdd fun i => (exponent F (x i)).toAdd
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd ((exponent F).map_mul (x i) (y i))

def integralLevel (r : ℕ) : Subgroup (Fin r → Fˣ) :=
  Subgroup.pi Set.univ fun _ => integralUnits F

theorem latticeValuation_surjective (r : ℕ) :
    Function.Surjective (latticeValuation F r) := by
  intro a
  choose x hx using fun i : Fin r => exponent_surjective F (Multiplicative.ofAdd (a.toAdd i))
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact congrArg Multiplicative.toAdd (hx i)

theorem latticeValuation_ker (r : ℕ) :
    (latticeValuation F r).ker = integralLevel F r := by
  ext x
  change (latticeValuation F r x = 1) ↔ ∀ i ∈ Set.univ, x i ∈ integralUnits F
  simp only [Set.mem_univ, forall_const, mem_integralUnits_iff,
    ← exponent_eq_one_iff]
  constructor
  · intro hx i
    have hi := congrArg (fun a : Multiplicative (Fin r → ℤ) => a.toAdd i) hx
    exact Multiplicative.toAdd.injective hi
  · intro hx
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd (hx i)

/-- Satake for the actual split torus (G_m)^r over F at its integral-unit
level. There are no roots and the Weyl group is trivial. -/
def satakeEquiv (r : ℕ) :
    Iwasawa.algebra (integralLevel F r) ≃ₐ[ℂ] AddMonoidAlgebra ℂ (Fin r → ℤ) := by
  rw [← latticeValuation_ker]
  exact Torus.satakeEquiv (latticeValuation F r) (latticeValuation_surjective F r)

end RepresentationTheory.Satake.GL3TorusIwasawa.LocalTorus

end

end OAI
