import OAI.AlgebraicGeometry.CycleClass.Thom.DVRFormalSmooth
import OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # DVR Stalk Smooth -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.DVRStalkSmooth.Constructions

noncomputable section

/-! Smoothness at an actual scheme point whose local ring is a discrete
valuation ring, over a characteristic-zero base field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk.Constructions

theorem mem_smoothLocus_of_stalk_dvr {k : Type} [Field k] [CharZero k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] : x ∈ f.smoothLocus := by
  let B := (Spec (.of k)).presheaf.stalk (f x)
  let b := (Spec (.of k)).presheaf.germ ⊤ (f x) (by trivial)
  let : IsIso b := FieldBaseStalk.Constructions.fieldBase_germ_isIso k (f x)
  let e : CommRingCat.of k ≅ B := (Scheme.ΓSpecIso (.of k)).symm ≪≫ asIso b
  let : Field B :=
    (MulEquiv.isField (Field.toIsField k) e.commRingCatIsoToRingEquiv.symm.toMulEquiv).toField
  let : CharZero B := charZero_of_injective_ringHom e.hom.hom.injective
  let : Algebra B (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType B (X.presheaf.stalk x) := LocallyOfFiniteType.stalkMap f x
  exact DVRFormalSmooth.Constructions.formallySmooth B (X.presheaf.stalk x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.DVRStalkSmooth.Constructions
