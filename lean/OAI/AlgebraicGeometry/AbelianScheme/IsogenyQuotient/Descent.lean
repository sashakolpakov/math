import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Descent.Construction

/-!
The quotient part of IsogenyQuotient, conditional on the precise invariant-morphism
universal property in FiniteDescent. The ambient category can be `Over S`, so these
arguments work on families and test all schemes, including nonreduced ones.
They do not assume that quotient polarizations or Hecke correspondences exist.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B H : C} [GrpObj A] [GrpObj B]

/-- The invariant-morphism clause of the supplied FiniteDescent conclusion. -/
def QuotientUniversalProperty (i : H ⟶ A) (f : A ⟶ B) : Prop :=
  ∀ (T : C) (g : A ⟶ T),
    (∀ (U : C) (a : U ⟶ A) (h : U ⟶ H),
      ((h ≫ i) * a) ≫ g = a ≫ g) →
    ∃! d : B ⟶ T, f ≫ d = g

/-- FiniteDescent's universal property supplies epimorphic cancellation. -/
theorem quotient_epi
    (i : H ⟶ A) (f : A ⟶ B) [IsMonHom f]
    (hkernel : i ≫ f = 1)
    (h_FiniteDescent : QuotientUniversalProperty i f) : Epi f := by
  constructor
  intro T g h hgh
  have hinvariant (U : C) (a : U ⟶ A) (k : U ⟶ H) :
      ((k ≫ i) * a) ≫ (f ≫ g) = a ≫ (f ≫ g) := by
    simp only [← Category.assoc, MonObj.mul_comp]
    simp only [Category.assoc, hkernel, MonObj.comp_one, one_mul]
  obtain ⟨d, _, hd⟩ := h_FiniteDescent T (f ≫ g) hinvariant
  exact (hd g rfl).trans (hd h hgh.symm).symm

/-- Endomorphisms preserving the kernel descend uniquely through the
actual quotient. This is the step used for the O_E-action. -/
theorem endomorphism_descent_of_FiniteDescent
    (i : H ⟶ A) (f : A ⟶ B) [IsMonHom f]
    (h_FiniteDescent : QuotientUniversalProperty i f)
    (a : A ⟶ A) [IsMonHom a]
    (hstable : i ≫ a ≫ f = 1) :
    ∃! b : B ⟶ B, f ≫ b = a ≫ f := by
  apply h_FiniteDescent B (a ≫ f)
  intro U x h
  simp only [← Category.assoc, MonObj.mul_comp]
  have hh : ((h ≫ i) ≫ a) ≫ f = 1 := by
    simpa only [Category.assoc, MonObj.comp_one] using
      congrArg (fun t => h ≫ t) hstable
  rw [hh, one_mul]

/-- If the kernel lies in A[n], multiplication by n factors through
the quotient. Both composites with this factor are multiplication by n. -/
theorem complementary_map_of_FiniteDescent
    [BraidedCategory C]
    [IsCommMonObj A]
    (i : H ⟶ A) (f : A ⟶ B) [IsMonHom f]
    (hkernel : i ≫ f = 1)
    (h_FiniteDescent : QuotientUniversalProperty i f)
    (n : ℕ) (hkilled : i ^ n = 1) :
    ∃! g : B ⟶ A,
      f ≫ g = (𝟙 A : A ⟶ A) ^ n ∧
      g ≫ f = (𝟙 B : B ⟶ B) ^ n := by
  have hinvariant (U : C) (a : U ⟶ A) (h : U ⟶ H) :
      ((h ≫ i) * a) ≫ (𝟙 A : A ⟶ A) ^ n =
        a ≫ (𝟙 A : A ⟶ A) ^ n := by
    simp only [MonObj.comp_pow, Category.comp_id, mul_pow]
    have hh : (h ≫ i) ^ n = 1 := by
      rw [← MonObj.comp_pow, hkilled, MonObj.comp_one]
    rw [hh, one_mul]
  obtain ⟨g, hg, hu⟩ := h_FiniteDescent A ((𝟙 A : A ⟶ A) ^ n) hinvariant
  have : Epi f := quotient_epi i f hkernel h_FiniteDescent
  refine ⟨g, ⟨hg, ?_⟩, fun g' hg' => hu g' hg'.1⟩
  apply (cancel_epi f).mp
  rw [← Category.assoc, hg, MonObj.pow_comp, Category.id_comp,
    MonObj.comp_pow, Category.comp_id]

omit [CartesianMonoidalCategory C] [GrpObj A] [GrpObj B] in
/-- The identity descends to the identity. -/
theorem descended_identity
    (f : A ⟶ B) [Epi f] (b : B ⟶ B)
    (hb : f ≫ b = (𝟙 A) ≫ f) : b = 𝟙 B := by
  apply (cancel_epi f).mp
  simpa using hb

omit [CartesianMonoidalCategory C] [GrpObj A] [GrpObj B] in
/-- Descended endomorphisms preserve composition, by quotient uniqueness. -/
theorem descended_composition
    (f : A ⟶ B) [Epi f]
    (a₁ a₂ : A ⟶ A) (b₁ b₂ b₁₂ : B ⟶ B)
    (h₁ : f ≫ b₁ = a₁ ≫ f)
    (h₂ : f ≫ b₂ = a₂ ≫ f)
    (h₁₂ : f ≫ b₁₂ = (a₁ ≫ a₂) ≫ f) :
    b₁₂ = b₁ ≫ b₂ := by
  apply (cancel_epi f).mp
  calc
    f ≫ b₁₂ = (a₁ ≫ a₂) ≫ f := h₁₂
    _ = a₁ ≫ (a₂ ≫ f) := Category.assoc _ _ _
    _ = a₁ ≫ (f ≫ b₂) := by rw [h₂]
    _ = (a₁ ≫ f) ≫ b₂ := (Category.assoc _ _ _).symm
    _ = (f ≫ b₁) ≫ b₂ := by rw [h₁]
    _ = f ≫ (b₁ ≫ b₂) := Category.assoc _ _ _

/-- Descended endomorphisms preserve the group-object addition law
(written multiplicatively by the group-object API). -/
theorem descended_addition
    (f : A ⟶ B) [Epi f] [IsMonHom f]
    (a₁ a₂ : A ⟶ A) (b₁ b₂ bsum : B ⟶ B)
    (h₁ : f ≫ b₁ = a₁ ≫ f)
    (h₂ : f ≫ b₂ = a₂ ≫ f)
    (hsum : f ≫ bsum = (a₁ * a₂) ≫ f) :
    bsum = b₁ * b₂ := by
  apply (cancel_epi f).mp
  rw [hsum, MonObj.mul_comp, MonObj.comp_mul, h₁, h₂]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Descent.Construction
