import OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization

/-! # CM Isogenies -/

namespace OAI.RepresentationTheory.Theta.Geometric.CMIsogenies

noncomputable section

/-! Every nonzero integral CM scalar acts by an actual finite etale
isogeny. A complementary integer produces multiplication by a positive
natural number, and its scheme geometry descends to the factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization
open scoped _root_.CategoryTheory.MonObj

theorem integral_scalar_complement {E : Type} [Field E] [NumberField E]
    (a : NumberField.RingOfIntegers E) (ha : a ≠ 0) :
    ∃ (n : ℕ), 0 < n ∧ ∃ b : NumberField.RingOfIntegers E, a * b = n ∧ b * a = n := by
  obtain ⟨n, hn, hi⟩ := AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization.exists_positive_integral_multiple E (a.val⁻¹)
  let b : NumberField.RingOfIntegers E := ⟨n • a.val⁻¹, hi⟩
  have ha' : a.val ≠ 0 := by exact_mod_cast ha
  have hab : a * b = (n : NumberField.RingOfIntegers E) := by
    apply Subtype.ext
    change a.val * (n • a.val⁻¹) = (n : E)
    rw [nsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ ha', mul_one]
  exact ⟨n, hn, b, hab, (mul_comm b a).trans hab⟩

theorem endSchemeMap_natCast {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A (n : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A) = (𝟙 A) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_add, ih, AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_one, pow_succ]

theorem finite_etale_surjective_of_complement {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (f h : A.scheme ⟶ A.scheme)
    (n : ℕ) (hn : 0 < n) (hfh : f ≫ h = (𝟙 A.scheme) ^ n)
    (hhf : h ≫ f = (𝟙 A.scheme) ^ n) :
    IsFinite f.left ∧ Etale f.left ∧ Surjective f.left := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnet : Etale (((𝟙 A.scheme) ^ n).left) :=
    AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A.scheme n
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) n)

  have hfh' : f.left ≫ h.left = ((𝟙 A.scheme) ^ n).left := congrArg Over.Hom.left hfh
  have hhf' : h.left ≫ f.left = ((𝟙 A.scheme) ^ n).left := congrArg Over.Hom.left hhf
  have : Etale (f.left ≫ h.left) := by rw [hfh']; exact hnet
  have : Etale (h.left ≫ f.left) := by rw [hhf']; exact hnet
  have : IsSeparated (h.left ≫ A.scheme.hom) := by rw [h.w]; infer_instance
  have : IsSeparated h.left := IsSeparated.of_comp h.left A.scheme.hom
  have : LocallyOfFiniteType (h.left ≫ A.scheme.hom) := by rw [h.w]; infer_instance
  have : LocallyOfFiniteType h.left := locallyOfFiniteType_of_comp h.left A.scheme.hom
  have : FormallyUnramified h.left := FormallyUnramified.of_comp h.left f.left
  have : Etale f.left := Etale.of_comp f.left h.left
  have : IsProper (f.left ≫ A.scheme.hom) := by rw [f.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left A.scheme.hom
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  refine ⟨AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified f.left, inferInstance, ?_⟩
  have hr : IsClopen (Set.range f.left) :=
    ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hr.eq_univ (Set.range_nonempty f.left))⟩

theorem integral_action_isogeny {E : Type} [Field E] [NumberField E] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (r : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.scheme)
    (a : NumberField.RingOfIntegers E) (ha : a ≠ 0) :
    IsFinite (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.scheme (r a)).left ∧
      Etale (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.scheme (r a)).left ∧
      Surjective (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.scheme (r a)).left := by
  obtain ⟨n, hn, b, hab, hba⟩ := integral_scalar_complement a ha
  apply finite_etale_surjective_of_complement A _ (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.scheme (r b)) n hn
  · rw [← AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul, ← map_mul, hba, map_natCast, endSchemeMap_natCast]
  · rw [← AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul, ← map_mul, hab, map_natCast, endSchemeMap_natCast]

end

end OAI.RepresentationTheory.Theta.Geometric.CMIsogenies
