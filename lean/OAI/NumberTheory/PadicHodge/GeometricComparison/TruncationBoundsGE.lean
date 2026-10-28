import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Truncation Bounds GE -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE.TruncationBounds

noncomputable section

/-! The native degree truncation is exhaustive and vanishes below its cutoff. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

theorem rightComp_surjective {D : Type*} [Category* D] {X Y Z : D}
    (g : Y ⟶ Z) [IsIso g] : Function.Surjective (fun f : X ⟶ Y => f ≫ g) := by
  intro f
  refine ⟨f ≫ inv g, ?_⟩
  change (f ≫ inv g) ≫ g = f
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℕ)

theorem isIso_inclusion_of_nonpositive (r : ℤ) (hr : r ≤ 0) :
    IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) := by
  have : ∀ n, IsIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r).f n) := by
    intro n
    change IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n)
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (show r ≤ (n : ℤ) by omega)]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

theorem extended_isStrictlyGE (r : ℤ) :
    CochainComplex.IsStrictlyGE
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).extend ComplexShape.embeddingUpNat) r := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases h0 : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hz : IsZero ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X n) := by
      change IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n)
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right (show ¬ r ≤ (n : ℤ) by omega)]
      exact isZero_zero C
    exact hz.of_iso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).extendXIso ComplexShape.embeddingUpNat rfl)
  · exact (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).isZero_extend_X ComplexShape.embeddingUpNat i (by
      intro n
      change (n : ℤ) ≠ i
      omega)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE.TruncationBounds
