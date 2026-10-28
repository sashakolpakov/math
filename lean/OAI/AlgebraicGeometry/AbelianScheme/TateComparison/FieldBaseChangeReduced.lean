import OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedFieldBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalGeneric
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Field Base Change Reduced -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChangeReduced

noncomputable section

/-! In characteristic zero, field base change of an integral scheme is
reduced, including infinite extensions. This applies to descent overlaps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem field_spectra_pullback_reduced {k F L : Type u}
    [Field k] [CharZero k] [Field F] [Field L]
    (f : Spec (.of F) ⟶ Spec (.of k)) (g : Spec (.of L) ⟶ Spec (.of k)) :
    IsReduced (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  let : Algebra k F := φ.hom.toAlgebra
  let : Algebra k L := ψ.hom.toAlgebra
  have : _root_.IsReduced (F ⊗[k] L) := NumberTheory.ArithmeticGroups.Lattices.ReducedFieldBaseChange.Construction.field_tensor_domain_charZero_reduced k F L
  have : IsReduced (Spec (.of (F ⊗[k] L))) := inferInstance
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k F L).hom

theorem charZero_fieldBaseChange_reduced {k L : Type u}
    [Field k] [CharZero k] [Field L] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (g : Spec (.of L) ⟶ Spec (.of k)) :
    IsReduced (pullback f g) := by
  let η := X.fromSpecStalk (genericPoint X)
  have : IsDominant η := Quotients.FiniteDescent.BirationalGeneric.Construction.BirationalGenericLift.dominant_generic X
  have : QuasiCompact η := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : IsSchemeTheoreticallyDominant η := IsSchemeTheoreticallyDominant.of_isDominant η
  have : Flat g := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective g
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) φ.hom
  have : IsReduced (pullback (η ≫ f) g) := field_spectra_pullback_reduced (η ≫ f) g
  have : IsReduced (pullback η (pullback.fst f g)) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso f g η).hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd η (pullback.fst f g))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChangeReduced
