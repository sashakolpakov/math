import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeBoundary
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Connecting Derived Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedCocycle

noncomputable section

/-! The connecting morphism is represented by the explicit signed resolution cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open _root_.CochainComplex _root_.CochainComplex.HomComplex DerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem derivedCocycleMap_eq_of_class_eq {A K : CochainComplex C ℤ} {n : ℤ}
    (z z' : Cocycle A K n) (h : CohomologyClass.mk z = CohomologyClass.mk z') :
    Q.map (Cocycle.equivHomShift.symm z) = Q.map (Cocycle.equivHomShift.symm z') := by
  have hh := congrArg CohomologyClass.toHom h
  simp only [CohomologyClass.toHom_mk] at hh
  apply (cancel_mono ((quotientCompQhIso C).inv.app (K⟦n⟧))).mp
  rw [quotientCompQhIso_inv_naturality, quotientCompQhIso_inv_naturality, hh]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  {K : CochainComplex C ℤ}
  (a : S.X₁ ⟶ K) (b : Cochain S.X₂ K 0) (z : Cocycle S.X₃ K 1)
  (hb : (Cochain.ofHom S.f).comp b (zero_add 0) = Cochain.ofHom a)
  (hd : δ 0 1 b = (Cochain.ofHom S.g).comp z.val (zero_add 1))

def connectingConeArrow : mappingCone S.f ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  (mappingCone.triangle S.f).mor₃

include hb hd in
theorem connectingDerivedCocycle_equation :
    Q.map (mappingCone.descShortComplex S) ≫ Q.map (Cocycle.equivHomShift.symm z) =
      -(Q.map (connectingConeArrow S) ≫ Q.map (a⟦(1 : ℤ)⟧')) := by
  have h := derivedCocycleMap_eq_of_class_eq _ _ (ConnectingConeBoundary.connectingCone_cohomologyClass S a b z hb hd)
  rw [Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Functor.map_comp] at h
  have he : connectingConeArrow S =
      -Cocycle.equivHomShift.symm (mappingCone.fst S.f) := by
    change Cocycle.equivHomShift.symm (-mappingCone.fst S.f) = _
    exact map_neg Cocycle.equivHomShift.symm _
  rw [he, Functor.map_neg, neg_comp, neg_neg]
  exact h

include hb hd in
theorem connectingDerivedCocycle :
    triangleOfSESδ hS ≫ (Q.map a)⟦(1 : ℤ)⟧' =
      -ShiftedHom.map (Cocycle.equivHomShift.symm z) Q := by
  have := mappingCone.quasiIso_descShortComplex hS
  apply (cancel_epi (Q.map (mappingCone.descShortComplex S))).mp
  rw [descShortComplex_triangleOfSESδ_assoc]
  have hn : (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ ≫ (Q.map a)⟦(1 : ℤ)⟧' =
      Q.map (a⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app K :=
    ((Q.commShiftIso (1 : ℤ)).hom.naturality a).symm
  erw [hn]
  change Q.map (connectingConeArrow S) ≫ Q.map (a⟦(1 : ℤ)⟧') ≫
    (Q.commShiftIso (1 : ℤ)).hom.app K = _
  rw [ShiftedHom.map, comp_neg, ← Category.assoc (Q.map (mappingCone.descShortComplex S))]
  have he := connectingDerivedCocycle_equation S a b z hb hd
  rw [he, neg_comp, neg_neg, Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedCocycle
