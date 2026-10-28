import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale

/-! # Tower -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-!
# FiniteEtale: multiplication and torsion in the geometric tower

Multiplication by p from level n+1 to level n is constructed from the
defining kernel property on the universal affine point. No surjectivity,
Cartier comparison, or classification is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj

universe u v

section Monoidal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B D : C} [MonObj A] [MonObj B] [MonObj D]

/-- A monomorphism of monoid objects detects the homomorphism laws. -/
theorem Tower.FiniteEtale.isMonHom_of_comp_mono (f : A ⟶ B) (g : B ⟶ D)
    [IsMonHom g] [Mono g] [IsMonHom (f ≫ g)] : IsMonHom f := by
  constructor
  · apply (cancel_mono g).mp
    simp only [Category.assoc, IsMonHom.one_hom]
  · apply (cancel_mono g).mp
    simp only [Category.assoc, IsMonHom.mul_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]

variable [BraidedCategory C] [IsCommMonObj B]

/-- Pointwise powers of a homomorphism into a commutative group object. -/
theorem Tower.FiniteEtale.isMonHom_pow (f : A ⟶ B) [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero =>
      change IsMonHom (1 : A ⟶ B)
      change IsMonHom (toUnit A ≫ η[B])
      infer_instance
  | succ n ih =>
      have : IsMonHom (f ^ n) := ih
      rw [pow_succ, Hom.mul_def]
      infer_instance

end Monoidal

variable {k : Type u} [Field k] {p h : ℕ}

variable (G : FiniteEtale.PDivisibleGroup k p h)

instance FiniteEtale.PDivisibleGroup.inclusion_mono (n : ℕ) : Mono (G.inclusion n) :=
  Over.mono_of_mono_left _

/-- The pth-power endomorphism of level n+1 factors through level n. -/
theorem FiniteEtale.PDivisibleGroup.exists_multiplyDown (n : ℕ) :
    ∃ f : (G.level (n + 1)).scheme ⟶ (G.level n).scheme,
      f ≫ G.inclusion n = (𝟙 (G.level (n + 1)).scheme) ^ p := by
  apply (G.kernel n (G.level (n + 1)).algebra _).mpr
  rw [← pow_mul, ← pow_succ']
  exact G.annihilated k (n + 1) _ (𝟙 _)

/-- Multiplication by p, with codomain lowered by one finite level. -/
def FiniteEtale.PDivisibleGroup.multiplyDown (n : ℕ) : (G.level (n + 1)).scheme ⟶ (G.level n).scheme :=
  (G.exists_multiplyDown n).choose

@[reassoc]
theorem FiniteEtale.PDivisibleGroup.multiplyDown_inclusion (n : ℕ) :
    G.multiplyDown n ≫ G.inclusion n = (𝟙 (G.level (n + 1)).scheme) ^ p :=
  (G.exists_multiplyDown n).choose_spec

instance FiniteEtale.PDivisibleGroup.multiplyDown_isMonHom (n : ℕ) : IsMonHom (G.multiplyDown n) := by
  have : IsMonHom ((𝟙 (G.level (n + 1)).scheme) ^ p) := Tower.FiniteEtale.isMonHom_pow _ _
  have : IsMonHom (G.multiplyDown n ≫ G.inclusion n) := by
    rw [G.multiplyDown_inclusion n]
    infer_instance
  exact Tower.FiniteEtale.isMonHom_of_comp_mono _ (G.inclusion n)

/-- The other composite is multiplication by p on the lower level. -/
@[reassoc]
theorem FiniteEtale.PDivisibleGroup.inclusion_multiplyDown (n : ℕ) :
    G.inclusion n ≫ G.multiplyDown n = (𝟙 (G.level n).scheme) ^ p := by
  apply (cancel_mono (G.inclusion n)).mp
  rw [Category.assoc, G.multiplyDown_inclusion, MonObj.comp_pow, Category.comp_id,
    MonObj.pow_comp, Category.id_comp]

/-- Multiplication and the transition maps commute in consecutive levels. -/
theorem FiniteEtale.PDivisibleGroup.multiplyDown_compatible (n : ℕ) :
    G.inclusion (n + 1) ≫ G.multiplyDown (n + 1) =
      G.multiplyDown n ≫ G.inclusion n := by
  rw [G.inclusion_multiplyDown, G.multiplyDown_inclusion]

/-- The geometric multiplication map acts as the pth power on every affine point. -/
theorem FiniteEtale.PDivisibleGroup.multiplyDown_points (n : ℕ) (R : CommAlgCat.{u} k)
    (x : FiniteEtale.affine k R ⟶ (G.level (n + 1)).scheme) :
    x ≫ G.multiplyDown n ≫ G.inclusion n = x ^ p := by
  rw [G.multiplyDown_inclusion, MonObj.comp_pow, Category.comp_id]

/-- Its pointwise kernel consists exactly of the p-torsion. -/
theorem FiniteEtale.PDivisibleGroup.multiplyDown_kernel (n : ℕ) (R : CommAlgCat.{u} k)
    (x : FiniteEtale.affine k R ⟶ (G.level (n + 1)).scheme) :
    x ≫ G.multiplyDown n = 1 ↔ x ^ p = 1 := by
  rw [← cancel_mono (G.inclusion n), Category.assoc,
    G.multiplyDown_points, MonObj.one_comp]

/-- The composite of r successive closed transition embeddings. -/
def FiniteEtale.PDivisibleGroup.inclusionIter (n : ℕ) : ∀ r, (G.level n).scheme ⟶ (G.level (n + r)).scheme
  | 0 => 𝟙 _
  | r + 1 => inclusionIter n r ≫ G.inclusion (n + r)

instance FiniteEtale.PDivisibleGroup.inclusionIter_isMonHom (n r : ℕ) : IsMonHom (G.inclusionIter n r) := by
  induction r with
  | zero => change IsMonHom (𝟙 _); infer_instance
  | succ r ih =>
      have : IsMonHom (G.inclusionIter n r) := ih
      change IsMonHom (G.inclusionIter n r ≫ G.inclusion (n + r))
      infer_instance

instance FiniteEtale.PDivisibleGroup.inclusionIter_mono (n r : ℕ) : Mono (G.inclusionIter n r) := by
  induction r with
  | zero => change Mono (𝟙 _); infer_instance
  | succ r ih =>
      have : Mono (G.inclusionIter n r) := ih
      change Mono (G.inclusionIter n r ≫ G.inclusion (n + r))
      infer_instance

/-- The n-th level is exactly the p^n-torsion in every later level. -/
theorem FiniteEtale.PDivisibleGroup.inclusionIter_kernel (n r : ℕ) (R : CommAlgCat.{u} k)
    (x : FiniteEtale.affine k R ⟶ (G.level (n + r)).scheme) :
    (∃ y : FiniteEtale.affine k R ⟶ (G.level n).scheme, y ≫ G.inclusionIter n r = x) ↔
      x ^ (p ^ n) = 1 := by
  induction r with
  | zero =>
      constructor
      · intro _; exact G.annihilated k n R x
      · intro _; exact ⟨x, Category.comp_id x⟩
  | succ r ih =>
      constructor
      · rintro ⟨y, rfl⟩
        rw [← MonObj.pow_comp, G.annihilated k n R y, MonObj.one_comp]
      · intro hx
        have hx' : x ^ (p ^ (n + r)) = 1 := by
          obtain ⟨d, hd⟩ := pow_dvd_pow p (Nat.le_add_right n r)
          rw [hd, pow_mul, hx, one_pow]
        obtain ⟨z, hz⟩ := (G.kernel (n + r) R x).mpr hx'
        have hzp : z ^ (p ^ n) = 1 := by
          apply (cancel_mono (G.inclusion (n + r))).mp
          rw [MonObj.pow_comp, hz, MonObj.one_comp]
          exact hx
        obtain ⟨y, hy⟩ := (ih z).mpr hzp
        refine ⟨y, ?_⟩
        change y ≫ (G.inclusionIter n r ≫ G.inclusion (n + r)) = x
        rw [← Category.assoc, hy, hz]

/-! Iterated transitions retain the actual closed-immersion property. -/

instance FiniteEtale.PDivisibleGroup.inclusionIter_closed (n r : ℕ) : IsClosedImmersion (G.inclusionIter n r).left := by
  induction r with
  | zero =>
    change IsClosedImmersion (𝟙 _)
    infer_instance
  | succ r ih =>
    have := ih
    change IsClosedImmersion ((G.inclusionIter n r).left ≫ (G.inclusion (n + r)).left)
    infer_instance

end

end OAI.AlgebraicGeometry.GroupSchemes
