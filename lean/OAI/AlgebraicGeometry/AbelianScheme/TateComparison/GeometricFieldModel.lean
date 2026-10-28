import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableResidueFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharZero.AddMonoidHom

/-! # Geometric Field Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel

noncomputable section

/-! Every geometric point over a countable characteristic-zero base has
a countable algebraically closed field of definition that also embeds
in ℂ. This does not require the original geometric field to be countable. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure CountableGeometricModel {k : Type} [Field k] {X : Scheme}
    (x : Spec (.of k) ⟶ X) where
  field : Type
  [fieldStructure : Field field]
  [countable : Countable field]
  [charZero : CharZero field]
  [isAlgClosed : IsAlgClosed field]
  toOriginal : field →+* k
  toComplex : field →+* ℂ
  point : Spec (.of field) ⟶ X
  factor : Spec.map (CommRingCat.ofHom toOriginal) ≫ point = x

attribute [instance] CountableGeometricModel.fieldStructure
  CountableGeometricModel.countable CountableGeometricModel.charZero
  CountableGeometricModel.isAlgClosed

theorem geometricPoint_has_countable_model
    (K : Type) [Field K] [CharZero K] [Countable K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    {k : Type} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) :
    Nonempty (CountableGeometricModel x) := by
  let z := Scheme.SpecToEquivOfField k X x
  let R := X.residueField z.1
  let : Algebra R k := z.2.hom.toAlgebra
  have : Countable R := CountableResidueFields.countable_scheme_residueField K f z.1
  let j : K →+* R := (Spec.preimage (X.fromSpecResidueField z.1 ≫ f)).hom
  have : CharZero R := CharZero.of_addMonoidHom j.toAddMonoidHom j.map_one j.injective
  let L := AlgebraicClosure R
  have : Countable L := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max R L).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  let ι : L →ₐ[R] k := IsAlgClosed.lift
  obtain ⟨κ⟩ := CountableComplexEmbedding.countable_field_has_complex_embedding L
  refine ⟨{
    field := L
    toOriginal := ι.toRingHom
    toComplex := κ
    point := Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ X.fromSpecResidueField z.1
    factor := ?_ }⟩
  rw [← Spec.map_comp_assoc]
  have hι : CommRingCat.ofHom (algebraMap R L) ≫ CommRingCat.ofHom ι.toRingHom = z.2 := by
    apply CommRingCat.hom_ext
    exact ι.comp_algebraMap
  rw [hι]
  exact (Scheme.SpecToEquivOfField k X).symm_apply_apply x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFieldModel
