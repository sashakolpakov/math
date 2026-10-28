import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion
import Mathlib.GroupTheory.Coset.Basic

/-! # Multiplication -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction

noncomputable section

/-!
Finiteness of multiplication maps from finiteness of their torsion kernels.
These are supporting results for Openness, independent of the openness statement.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme}

/-- A field-valued point over S is a rational point after base change. -/
def fieldPointPullbackEquiv (T : Over S)
    {K : Type*} [Field K] (x : Spec (.of K) ⟶ S) :
    (Over.mk x ⟶ T) ≃
      {p : Spec (.of K) ⟶ pullback T.hom x //
        p ≫ pullback.snd T.hom x = 𝟙 _} where
  toFun f := ⟨pullback.lift f.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
  invFun p := Over.homMk (p.val ≫ pullback.fst T.hom x) (by
    change (p.val ≫ pullback.fst T.hom x) ≫ T.hom = x
    rw [Category.assoc, pullback.condition, ← Category.assoc, p.prop, Category.id_comp])
  left_inv f := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.prop.symm

/-- A finite S-scheme has finitely many points valued in any algebraically
closed field over S. -/
theorem finite_fieldPoints_of_isFinite (T : Over S) [IsFinite T.hom]
    {K : Type*} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ S) :
    Finite (Over.mk x ⟶ T) := by
  have h := (pullback.snd T.hom x).finite_preimage
    (Set.toFinite (Set.univ : Set (Spec (.of K))))
  simp only [Set.preimage_univ] at h
  have : Finite ↥(pullback T.hom x) := Set.finite_univ_iff.mp h
  exact Finite.of_equiv _
    ((fieldPointPullbackEquiv T x).trans (pointEquivClosedPoint (pullback.snd T.hom x))).symm

variable (A : Over S) [GrpObj A] [IsCommMonObj A]

/-- Multiplication by n as a morphism of S-schemes. -/
abbrev multiplicationMap (n : ℕ) : A ⟶ A := (𝟙 A) ^ n

instance multiplicationMap_isProper (n : ℕ) [IsProper A.hom] :
    IsProper (multiplicationMap A n).left := by
  have : IsProper ((multiplicationMap A n).left ≫ A.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ A.hom

/-- Each nonempty power fiber of the point group is a translate of the kernel. -/
theorem finite_powerFiber_of_finite_torsionPoints (n : ℕ) (T : Over S)
    [Finite (T ⟶ DefinitionsTorsion.Construction.torsionScheme A n)] (y : T ⟶ A) :
    Finite {x : T ⟶ A // x ^ n = y} := by
  let f : (T ⟶ A) →* (T ⟶ A) :=
    { toFun := fun x => x ^ n
      map_one' := one_pow n
      map_mul' := fun x z => mul_pow x z n }
  have : Finite f.ker := Finite.of_equiv _ (DefinitionsTorsion.Construction.torsionPointsEquiv A n T)
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    exact Finite.of_equiv _ (f.fiberEquivKer x).symm
  · have : IsEmpty {x : T ⟶ A // x ^ n = y} :=
      ⟨fun x => hy ⟨x.val, x.prop⟩⟩
    infer_instance

/-- Points in a geometric fiber of multiplication inject into a power fiber
of the group of S-valued morphisms. -/
def multiplicationFiberPointEmbedding (n : ℕ) {P : Scheme} (a : P ⟶ A.left) :
    (Over.mk a ⟶ Over.mk (multiplicationMap A n).left) ↪
      {x : Over.mk (a ≫ A.hom) ⟶ A //
        x ^ n = Over.homMk a (by rfl)} where
  toFun f := by
    let x : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk f.left (by
      change f.left ≫ A.hom = a ≫ A.hom
      calc
        f.left ≫ A.hom = f.left ≫ ((multiplicationMap A n).left ≫ A.hom) :=
          congrArg (fun g => f.left ≫ g) (multiplicationMap A n).w.symm
        _ = (f.left ≫ (multiplicationMap A n).left) ≫ A.hom :=
          (Category.assoc _ _ _).symm
        _ = a ≫ A.hom := congrArg (fun g => g ≫ A.hom) f.w)
    refine ⟨x, ?_⟩
    have h : x ≫ multiplicationMap A n =
        (Over.homMk a (by rfl) : Over.mk (a ≫ A.hom) ⟶ A) := by
      apply Over.OverMorphism.ext
      exact f.w
    simpa only [multiplicationMap, MonObj.comp_pow, Category.comp_id] using h
  inj' := by
    intro f g h
    apply Over.OverMorphism.ext
    exact congrArg (fun x => x.val.left) h

/-- When the torsion scheme is finite, multiplication has finite geometric fibers. -/
theorem finite_multiplication_geometric_points (n : ℕ)
    [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] (y : A.left) :
    Finite (DefinitionsTorsion.geometricPoint A.left y ⟶
      Over.mk (multiplicationMap A n).left) := by
  let a := (DefinitionsTorsion.geometricPoint A.left y).hom
  have : Finite (Over.mk (a ≫ A.hom) ⟶ DefinitionsTorsion.Construction.torsionScheme A n) :=
    finite_fieldPoints_of_isFinite (DefinitionsTorsion.Construction.torsionScheme A n)
      (K := AlgebraicClosure (A.left.residueField y)) (a ≫ A.hom)
  have := finite_powerFiber_of_finite_torsionPoints A n
    (Over.mk (a ≫ A.hom)) (Over.homMk a (by rfl))
  exact Finite.of_injective (multiplicationFiberPointEmbedding A n a)
    (multiplicationFiberPointEmbedding A n a).injective

/-- A proper commutative group scheme has finite multiplication-by-n
whenever its n-torsion scheme is finite over the base. -/
theorem isFinite_multiplication_of_isFinite_torsion (n : ℕ)
    [IsProper A.hom] [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] :
    IsFinite (multiplicationMap A n).left := by
  have : LocallyQuasiFinite (multiplicationMap A n).left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    have := finite_multiplication_geometric_points A n y
    have : LocallyOfFiniteType (Over.mk (multiplicationMap A n).left).hom := by
      change LocallyOfFiniteType (multiplicationMap A n).left
      infer_instance
    exact DefinitionsTorsion.Construction.finite_preimage_of_finite_geometric_points
      (Over.mk (multiplicationMap A n).left) y
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction
