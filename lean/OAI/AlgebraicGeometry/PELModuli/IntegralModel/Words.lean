import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Words -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Words.DifferenceWords

noncomputable section

/-!
Finite sums of point differences as actual arithmetic scheme morphisms.
The formula on every test scheme is proved directly from the group law.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {B : Scheme.{u}}

abbrev domain (X : Over B) : ℕ → Over B
  | 0 => 𝟙_ (Over B)
  | n + 1 => domain X n ⊗ (X ⊗ X)

def difference {X A : Over B} [GrpObj A] (a : X ⟶ A) : X ⊗ X ⟶ A :=
  (fst _ _ ≫ a) / (snd _ _ ≫ a)

def map {X A : Over B} [GrpObj A] (a : X ⟶ A) : (n : ℕ) → DifferenceWords.domain X n ⟶ A
  | 0 => 1
  | n + 1 => (fst _ _ ≫ map a n) * (snd _ _ ≫ difference a)

/-- The word domain represents tuples of pairs of points on every test scheme. -/
def pointsEquiv (Q X : Over B) : (n : ℕ) →
    (Q ⟶ DifferenceWords.domain X n) ≃ (Fin n → (Q ⟶ X) × (Q ⟶ X))
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => toUnit Q
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => by funext i; exact Fin.elim0 i }
  | n + 1 => {
      toFun := fun p => Fin.cases
        ((p ≫ snd _ _) ≫ fst _ _, (p ≫ snd _ _) ≫ snd _ _)
        (pointsEquiv Q X n (p ≫ fst _ _))
      invFun := fun z => lift ((pointsEquiv Q X n).symm (fun i => z i.succ))
        (lift (z 0).1 (z 0).2)
      left_inv := fun p => by
        apply hom_ext
        · simp
        · apply hom_ext <;> simp
      right_inv := fun z => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp }

instance domain_proper (X : Over B) [IsProper X.hom] (n : ℕ) :
    IsProper (DifferenceWords.domain X n).hom := by
  induction n with
  | zero => change IsProper (𝟙 B); infer_instance
  | succ n ih => change IsProper (DifferenceWords.domain X n ⊗ (X ⊗ X)).hom; dsimp; infer_instance

instance domain_smooth (X : Over B) [Smooth X.hom] (n : ℕ) :
    Smooth (DifferenceWords.domain X n).hom := by
  induction n with
  | zero => change Smooth (𝟙 B); infer_instance
  | succ n ih => change Smooth (DifferenceWords.domain X n ⊗ (X ⊗ X)).hom; dsimp; infer_instance

instance map_proper {X A : Over B} [GrpObj A] [IsProper X.hom]
    [IsSeparated A.hom] (a : X ⟶ A) (n : ℕ) : IsProper (DifferenceWords.map a n).left := by
  have : IsProper ((DifferenceWords.map a n).left ≫ A.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp _ A.hom

/-- Evaluation is the exact finite sum used in the IntegralModel specification. -/
theorem map_points {X A : Over B} [GrpObj A] [IsCommMonObj A]
    (a : X ⟶ A) (Q : Over B) (n : ℕ) (p : Q ⟶ DifferenceWords.domain X n) :
    Additive.ofMul (p ≫ DifferenceWords.map a n) =
      ∑ i : Fin n,
        (Additive.ofMul ((DifferenceWords.pointsEquiv Q X n p i).1 ≫ a) -
         Additive.ofMul ((DifferenceWords.pointsEquiv Q X n p i).2 ≫ a)) := by
  induction n with
  | zero => simp [DifferenceWords.map]
  | succ n ih =>
    simp only [DifferenceWords.map, MonObj.comp_mul, difference, GrpObj.comp_div, Fin.sum_univ_succ]
    change Additive.ofMul ((p ≫ fst _ _) ≫ DifferenceWords.map a n) +
      (Additive.ofMul (((p ≫ snd _ _) ≫ fst _ _) ≫ a) -
        Additive.ofMul (((p ≫ snd _ _) ≫ snd _ _) ≫ a)) = _
    rw [ih]
    simp only [DifferenceWords.pointsEquiv, Equiv.coe_fn_mk, Fin.cases_zero, Fin.cases_succ]
    exact add_comm _ _

theorem sum_surjective_iff {X A : Over B} [GrpObj A] [IsCommMonObj A]
    (a : X ⟶ A) (Q : Over B) (n : ℕ) :
    Function.Surjective
      (fun z : Fin n → (Q ⟶ X) × (Q ⟶ X) =>
        ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a))) ↔
    Function.Surjective (fun p : Q ⟶ DifferenceWords.domain X n => p ≫ DifferenceWords.map a n) := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (Additive.ofMul y)
    refine ⟨(DifferenceWords.pointsEquiv Q X n).symm z, ?_⟩
    apply Additive.ofMul.injective
    rw [map_points, Equiv.apply_symm_apply]
    exact hz
  · intro h y
    obtain ⟨p, hp⟩ := h y.toMul
    change p ≫ DifferenceWords.map a n = y.toMul at hp
    refine ⟨DifferenceWords.pointsEquiv Q X n p, ?_⟩
    dsimp only
    rw [← map_points, hp]
    rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Words.DifferenceWords
