import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Geometric Division -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision

noncomputable section

/-! Multiplication by a nonzero integer on a characteristic-zero abelian
variety is an actual finite etale surjective morphism. Geometric points
therefore have division lifts, and Tate evaluation reaches every torsion point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [CharZero k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (n : ℕ) [NeZero n]

theorem field_integer_unit_at_stalk (x : Spec (.of k)) :
    IsUnit (n : (Spec (.of k)).presheaf.stalk x) := by
  let c : k →+* (Spec (.of k)).presheaf.stalk x :=
    ((Spec (.of k)).presheaf.germ ⊤ x (by trivial)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hu : IsUnit (n : k) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [map_natCast] using hu.map c

theorem multiplication_finite_etale :
    IsFinite (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) ∧
      Etale (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) := by
  let : Etale (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) :=
    TorsionQuotient.Etale.TorsionEtale.power_etale A.scheme n (field_integer_unit_at_stalk n)
  let : IsProper (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) :=
    TorsionQuotient.Quasi.TorsionGeometry.power_isProper A.scheme n
  exact ⟨TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _, inferInstance⟩

theorem multiplication_surjective :
    Surjective (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  let f := ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left
  have : IsFinite f := (multiplication_finite_etale A n).1
  have : Etale f := (multiplication_finite_etale A n).2
  have hc : IsClopen (Set.range f) := ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  have hr : Set.range f = Set.univ := hc.eq_univ (Set.range_nonempty f)
  exact ⟨Set.range_eq_univ.mp hr⟩

def multiplicationIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A A where
  hom := (𝟙 A.scheme) ^ n
  preservesGroup := inferInstance
  finite := (multiplication_finite_etale A n).1
  flat := by
    have : Etale (((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left) :=
      (multiplication_finite_etale A n).2
    infer_instance
  surjective := multiplication_surjective A n

theorem geometricPoint_divisible [IsAlgClosed k] (x : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)) :
    ∃ y, n • y = x := by
  obtain ⟨y, hy⟩ := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective
    (multiplicationIsogeny A n) (𝟙 (Spec (.of k))) x.toMul
  refine ⟨Additive.ofMul y, ?_⟩
  change y ≫ (𝟙 A.scheme) ^ n = x.toMul at hy
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  change y ^ n = x.toMul
  simpa only [MonObj.comp_pow, Category.comp_id] using hy

theorem geometricTate_evaluate_surjective [IsAlgClosed k] (q : ℕ) [Fact q.Prime] (m : ℕ) :
    Function.Surjective (Evaluation.Tate.evaluate (H := Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)) q m) :=
  Evaluation.Tate.evaluate_surjective q (geometricPoint_divisible A q) m

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision
