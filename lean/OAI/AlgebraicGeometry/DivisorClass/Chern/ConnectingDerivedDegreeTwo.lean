import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeDegreeTwo

/-! # Connecting Derived Degree Two -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedDegreeTwo

noncomputable section

/-! Actual derived composition of a connecting morphism and a degree-one cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open _root_.CochainComplex _root_.CochainComplex.HomComplex DerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem derivedCocycleShiftedMap_eq_of_class_eq {A K : CochainComplex C ℤ} {n : ℤ}
    (z z' : Cocycle A K n) (h : CohomologyClass.mk z = CohomologyClass.mk z') :
    ShiftedHom.map (Cocycle.equivHomShift.symm z) Q =
      ShiftedHom.map (Cocycle.equivHomShift.symm z') Q :=
  congrArg (fun f => f ≫ (Q.commShiftIso n).hom.app K) (ConnectingDerivedCocycle.derivedCocycleMap_eq_of_class_eq z z' h)

variable (S : ShortComplex (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
  (a : Cocycle S.X₁ K 1) (b : Cochain S.X₂ K 1) (z : Cocycle S.X₃ K 2)
  (hb : (Cochain.ofHom S.f).comp b (zero_add 1) = a.val)
  (hd : δ 1 2 b = (Cochain.ofHom S.g).comp z.val (zero_add 2))

include hb hd in
theorem connectingCone_degreeTwo_derived :
    Q.map (mappingCone.descShortComplex S) ≫ ShiftedHom.map (Cocycle.equivHomShift.symm z) Q =
      ShiftedHom.comp (ShiftedHom.map (ConnectingDerivedCocycle.connectingConeArrow S) Q)
        (ShiftedHom.map (Cocycle.equivHomShift.symm a) Q) (show (1 : ℤ) + 1 = 2 from rfl) := by
  have hc : ShiftedHom.map (ConnectingDerivedCocycle.connectingConeArrow S) Q =
      -ShiftedHom.map (Cocycle.equivHomShift.symm (mappingCone.fst S.f)) Q := by
    change ShiftedHom.map (Cocycle.equivHomShift.symm (-mappingCone.fst S.f)) Q = _
    simp only [map_neg, ShiftedHom.map, Functor.map_neg, neg_comp]
  calc
    _ = ShiftedHom.map (Cocycle.equivHomShift.symm (z.precomp (mappingCone.descShortComplex S))) Q := by
      rw [Cocycle.equivHomShift_symm_precomp]
      simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
    _ = ShiftedHom.map (Cocycle.equivHomShift.symm (-CocycleComposition.cocycleOneComp (mappingCone.fst S.f) a)) Q :=
      derivedCocycleShiftedMap_eq_of_class_eq _ _
        (ConnectingConeDegreeTwo.connectingCone_degreeTwo_cohomologyClass S a b z hb hd)
    _ = -ShiftedHom.map (Cocycle.equivHomShift.symm (CocycleComposition.cocycleOneComp (mappingCone.fst S.f) a)) Q := by
      simp only [map_neg, ShiftedHom.map, Functor.map_neg, neg_comp]
    _ = -ShiftedHom.comp (ShiftedHom.map (Cocycle.equivHomShift.symm (mappingCone.fst S.f)) Q)
        (ShiftedHom.map (Cocycle.equivHomShift.symm a) Q) (show (1 : ℤ) + 1 = 2 from rfl) := by
      rw [CocycleComposition.cocycleOneComp_shiftHom, ShiftedHom.map_comp]
    _ = _ := by rw [hc, ShiftedHom.neg_comp]

include hb hd in
theorem connectingDerivedDegreeTwo (hS : S.ShortExact) :
    ShiftedHom.comp (triangleOfSESδ hS) (ShiftedHom.map (Cocycle.equivHomShift.symm a) Q)
      (show (1 : ℤ) + 1 = 2 from rfl) = ShiftedHom.map (Cocycle.equivHomShift.symm z) Q := by
  have := mappingCone.quasiIso_descShortComplex hS
  apply (cancel_epi (Q.map (mappingCone.descShortComplex S))).mp
  calc
    _ = ShiftedHom.comp (Q.map (mappingCone.descShortComplex S) ≫ triangleOfSESδ hS)
        (ShiftedHom.map (Cocycle.equivHomShift.symm a) Q) (show (1 : ℤ) + 1 = 2 from rfl) := by
      simp only [ShiftedHom.comp, Category.assoc]
    _ = ShiftedHom.comp (ShiftedHom.map (ConnectingDerivedCocycle.connectingConeArrow S) Q)
        (ShiftedHom.map (Cocycle.equivHomShift.symm a) Q) (show (1 : ℤ) + 1 = 2 from rfl) := by
      rw [descShortComplex_triangleOfSESδ]
      rfl
    _ = _ := (connectingCone_degreeTwo_derived S a b z hb hd).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedDegreeTwo
