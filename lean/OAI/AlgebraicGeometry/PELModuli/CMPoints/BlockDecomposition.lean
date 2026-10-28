import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Block Decomposition -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition

noncomputable section

/-! The split integral projectors give a product decomposition of actual
torsion points on every test scheme, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

include hsplit in
theorem action_eq_of_coordinates (n : ℕ)
    (b c : NumberField.RingOfIntegers E)
    (hbc : j.residueCoordinates iota n b = j.residueCoordinates iota n c)
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1) :
    x ≫ ρ.map b = x ≫ ρ.map c := by
  apply BlocksProjectors.action_eq_of_congruence A ρ b c (q ^ n) _ T x hx
  rw [Nat.cast_pow, ← (hsplit n).2]
  change j.residueCoordinates iota n (b - c) = 0
  rw [map_sub, hbc, sub_self]

theorem projector_idempotent_on_torsion (n : ℕ) (τ : Gal(E/ℚ))
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1) :
    (x ≫ ρ.map (j.projector iota hsplit n τ)) ≫
      ρ.map (j.projector iota hsplit n τ) = x ≫ ρ.map (j.projector iota hsplit n τ) := by
  classical
  rw [Category.assoc, ← ρ.map_mul]
  apply action_eq_of_coordinates j iota hsplit A ρ n _ _ _ T x hx
  rw [map_mul, j.projector_coordinates]
  ext υ
  by_cases h : υ = τ <;> simp [h]

theorem projector_orthogonal_on_torsion (n : ℕ) (τ υ : Gal(E/ℚ)) (h : τ ≠ υ)
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1) :
    (x ≫ ρ.map (j.projector iota hsplit n τ)) ≫
      ρ.map (j.projector iota hsplit n υ) = 1 := by
  classical
  rw [Category.assoc, ← ρ.map_mul]
  have he : j.residueCoordinates iota n
      (j.projector iota hsplit n υ * j.projector iota hsplit n τ) =
        j.residueCoordinates iota n 0 := by
    rw [map_mul, j.projector_coordinates, j.projector_coordinates, map_zero]
    ext ν
    by_cases hν : ν = τ
    · subst ν
      simp [h]
    · simp [hν]
  rw [action_eq_of_coordinates j iota hsplit A ρ n _ 0 he T x hx,
    ρ.map_zero, MonObj.comp_one]

def torsionProjection (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S) :
    A.torsionPoints (q ^ n) T →* BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T where
  toFun x := ⟨x.val ≫ ρ.map (j.projector iota hsplit n τ),
    (BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ T _).mpr ⟨by
      have hx : x.val ^ (q ^ n) = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp],
      projector_idempotent_on_torsion j iota hsplit A ρ n τ T x.val x.property⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

theorem block_projector_self (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S)
    (x : BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) :
    x.val ≫ ρ.map (j.projector iota hsplit n τ) = x.val :=
  ((BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ T x.val).mp x.property).2

theorem block_projector_other (n : ℕ) (τ υ : Gal(E/ℚ)) (h : τ ≠ υ)
    (T : Over S) (x : BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) :
    x.val ≫ ρ.map (j.projector iota hsplit n υ) = 1 := by
  have hx := projector_orthogonal_on_torsion j iota hsplit A ρ n τ υ h T x.val x.property.1
  rw [block_projector_self j iota hsplit A ρ n τ T x] at hx
  exact hx

omit [NumberField E] [Algebra ℚ E] in
theorem integralAction_sum_on_points {Idx : Type*} (s : Finset Idx)
    (b : Idx → NumberField.RingOfIntegers E) (T : Over S) (x : T ⟶ A.scheme) :
    x ≫ ρ.map (∑ i ∈ s, b i) = ∏ i ∈ s, x ≫ ρ.map (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, ρ.map_zero, MonObj.comp_one]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, ρ.map_add, MonObj.comp_mul, ih]

theorem torsion_projectors_sum (n : ℕ) (T : Over S)
    (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1) :
    (∏ τ : Gal(E/ℚ), x ≫ ρ.map (j.projector iota hsplit n τ)) = x := by
  classical
  rw [← integralAction_sum_on_points A ρ]
  have hs : j.residueCoordinates iota n (∑ τ, j.projector iota hsplit n τ) =
      j.residueCoordinates iota n 1 := by
    simp only [map_sum, j.projector_coordinates, map_one]
    ext υ
    simp [Finset.sum_apply, Pi.single_apply]
  rw [action_eq_of_coordinates j iota hsplit A ρ n _ 1 hs T x hx, ρ.map_one, Category.comp_id]

def assembleBlocks (n : ℕ) (T : Over S) :
    (∀ τ : Gal(E/ℚ), BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) →*
      A.torsionPoints (q ^ n) T where
  toFun x := ⟨∏ τ, (x τ).val, by
    change (∏ τ, (x τ).val) ^ (q ^ n) = 1
    rw [← Finset.prod_pow]
    simp only [(x _).property.1, Finset.prod_const_one]⟩
  map_one' := by apply Subtype.ext; exact Finset.prod_const_one
  map_mul' x y := by apply Subtype.ext; exact Finset.prod_mul_distrib

theorem assemble_torsionProjections (n : ℕ) (T : Over S)
    (x : A.torsionPoints (q ^ n) T) :
    assembleBlocks j iota A ρ n T (fun τ => torsionProjection j iota hsplit A ρ n τ T x) = x := by
  apply Subtype.ext
  exact torsion_projectors_sum j iota hsplit A ρ n T x.val x.property

theorem torsionProjection_assemble (n : ℕ) (T : Over S)
    (x : ∀ τ : Gal(E/ℚ), BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) (υ : Gal(E/ℚ)) :
    torsionProjection j iota hsplit A ρ n υ T (assembleBlocks j iota A ρ n T x) = x υ := by
  classical
  apply Subtype.ext
  let f : (T ⟶ A.scheme) →* (T ⟶ A.scheme) := {
    toFun a := a ≫ ρ.map (j.projector iota hsplit n υ)
    map_one' := MonObj.one_comp _
    map_mul' a b := MonObj.mul_comp a b _ }
  change f (∏ τ, (x τ).val) = (x υ).val
  rw [map_prod]
  rw [Finset.prod_eq_single υ]
  · exact block_projector_self j iota hsplit A ρ n υ T (x υ)
  · intro τ _ hτ
    exact block_projector_other j iota hsplit A ρ n τ υ hτ T (x τ)
  · simp

/-- The product decomposition is an isomorphism of actual groups of
torsion points, uniformly over every test scheme. -/
def torsionBlockEquiv (n : ℕ) (T : Over S) :
    A.torsionPoints (q ^ n) T ≃*
      (∀ τ : Gal(E/ℚ), BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T) where
  toFun x τ := torsionProjection j iota hsplit A ρ n τ T x
  invFun := assembleBlocks j iota A ρ n T
  left_inv := assemble_torsionProjections j iota hsplit A ρ n T
  right_inv x := funext (torsionProjection_assemble j iota hsplit A ρ n T x)
  map_mul' x y := funext (fun τ => (torsionProjection j iota hsplit A ρ n τ T).map_mul x y)

def productBlockFunctor (n : ℕ) : (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (∀ τ : Gal(E/ℚ), BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n T.unop)
  map f := GrpCat.ofHom {
    toFun x τ := BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f.unop (x τ)
    map_one' := funext (fun τ => (BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f.unop).map_one)
    map_mul' x y := funext (fun τ =>
      (BlocksProjectors.blockPullback A ρ (j.localCharacter iota τ) n f.unop).map_mul (x τ) (y τ)) }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext τ
    exact Subtype.ext (Category.id_comp (x τ).val)
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext τ
    exact Subtype.ext (Category.assoc _ _ (x τ).val)

/-- The product decomposition is natural on the entire big test category. -/
def torsionBlockIso (n : ℕ) :
    A.torsionFunctor (q ^ n) ≅ productBlockFunctor j iota A ρ n :=
  NatIso.ofComponents (fun T => (torsionBlockEquiv j iota hsplit A ρ n T.unop).toGrpIso) (by
    intro T U f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext τ
    exact Subtype.ext (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition
