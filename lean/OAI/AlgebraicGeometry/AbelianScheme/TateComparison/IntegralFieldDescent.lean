import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldGeometricDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FaithfulGroupMap
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Integral Field Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralFieldDescent

noncomputable section

/-! Descent of actual integral algebraic group endomorphisms from
compatible geometric point values over a field extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k L : Type u} [Field k] [CharZero k] [Field L]
  (p : Spec (.of L) ⟶ Spec (.of k)) (A : Over (Spec (.of k)))

def fieldEndUnderlying (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) :
    FieldGeometricDescent.fieldSource p A ⟶ A :=
  Over.homMk (φ.left ≫ pullback.fst A.hom p) (by
    change (φ.left ≫ pullback.fst A.hom p) ≫ A.hom = pullback.fst A.hom p ≫ A.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun a : pullback A.hom p ⟶ Spec (.of L) => a ≫ p) φ.w)

omit [CharZero k] in
theorem fieldEndUnderlying_baseChange_eq
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) (f : A ⟶ A)
    (hf : FieldGeometricDescent.fieldSourceProjection p A ≫ f = fieldEndUnderlying p A φ) :
    (Over.pullback p).map f = φ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (congrArg Over.Hom.left hf)
  · exact ((Over.pullback p).map f).w.trans φ.w.symm

theorem integralEnd_descends_of_geometric_compatibility
    [GrpObj A] [IsCommMonObj A] [IsIntegral (pullback A.hom p)] [IsSeparated A.hom]
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) [IsMonHom φ]
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ Spec (.of k)) (x y : Over.mk b ⟶ FieldGeometricDescent.fieldSource p A),
      x ≫ FieldGeometricDescent.fieldSourceProjection p A = y ≫ FieldGeometricDescent.fieldSourceProjection p A →
        x ≫ fieldEndUnderlying p A φ = y ≫ fieldEndUnderlying p A φ) :
    ∃ e : End.IntegralEnd A,
      BaseChange.endBaseChange A p e = End.endOfSchemeMap ((Over.pullback p).obj A) φ := by
  obtain ⟨f, hf, _⟩ := FieldGeometricDescent.fieldGeometricDescent p A A (fieldEndUnderlying p A φ) hφ
  have he : (Over.pullback p).map f = φ := fieldEndUnderlying_baseChange_eq p A φ f hf
  have : Flat p := by
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective p
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) ρ.hom
  have : Surjective p := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact p := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : (Over.pullback p).Faithful := inferInstance
  have : IsMonHom ((Over.pullback p).map f) := he.symm ▸ inferInstanceAs (IsMonHom φ)
  have : IsMonHom f := FaithfulGroupMap.isMonHom_of_faithful_map (Over.pullback p) f
  refine ⟨End.endOfSchemeMap A f, ?_⟩
  apply End.endSchemeMap_injective ((Over.pullback p).obj A)
  rw [BaseChange.endBaseChange_schemeMap, End.endSchemeMap_ofSchemeMap, End.endSchemeMap_ofSchemeMap]
  exact he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralFieldDescent
