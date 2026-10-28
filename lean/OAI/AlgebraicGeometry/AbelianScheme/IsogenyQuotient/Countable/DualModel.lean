import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedPair
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.ParameterLines
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedProductRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcMixedPoincareRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFunctions

/-! # Dual Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualModel.Construction

noncomputable section

/-! Full native dual abelian data of a geometric polarized abelian
variety have a countable algebraically closed field of definition,
including the actual Poincare line and both original group comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure CountableDualModel {k : Type} [Field k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) where
  field : Subfield k
  [countable : Countable field]
  [algebraicallyClosed : IsAlgClosed field]
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of field))
  dual : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData abelian
  sourceRecovery : A.scheme ≅ (abelian.pullback (Spec.map (CommRingCat.ofHom field.subtype))).scheme
  dualRecovery : D.abelian.scheme ≅ (dual.abelian.pullback (Spec.map (CommRingCat.ofHom field.subtype))).scheme
  sourceGroup : IsMonHom sourceRecovery.hom
  dualGroup : IsMonHom dualRecovery.hom
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap (Spec.map (CommRingCat.ofHom field.subtype)) dualRecovery sourceRecovery)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf dual.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare

attribute [instance] CountableDualModel.countable CountableDualModel.algebraicallyClosed
  CountableDualModel.sourceGroup CountableDualModel.dualGroup

set_option backward.isDefEq.respectTransparency false in
theorem countable_polarized_dual_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    Nonempty (CountableDualModel A.abelian A.dual) := by
  obtain ⟨M⟩ := PolarizedPair.Construction.countable_polarized_pair_model_exists A
  let F := M.field
  let B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of F)) := M.family false
  let E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of F)) := M.family true
  let w := Spec.map (CommRingCat.ofHom F.subtype)
  let eA : A.abelian.scheme ≅ (B.pullback w).scheme := M.recovery false
  let eD : A.dual.abelian.scheme ≅ (E.pullback w).scheme := M.recovery true
  have : IsMonHom eA.hom := M.recovery_group false
  have : IsMonHom eD.hom := M.recovery_group true
  let X := E.scheme ⊗ B.scheme
  have : IsProper X.hom := inferInstanceAs
    (IsProper (pullback.fst E.scheme.hom B.scheme.hom ≫ E.scheme.hom))
  let c := StagedProductRecovery.Construction.recoveredProductParameterIso w E.scheme B.scheme eD eA
  let L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F k ⊗ X).left := A.dual.poincare.pullback c.inv
  obtain ⟨G, hG, hGa, hFG, JG, ⟨hJG⟩⟩ := ParameterLines.Construction.countable_parameter_line_model_exists F X L
  let : Countable G := hG
  let : IsAlgClosed G := hGa
  let v := Spec.map (CommRingCat.ofHom (Subfield.inclusion hFG))
  let u := Spec.map (CommRingCat.ofHom G.subtype)
  have hu : u ≫ v = w := (ParameterLines.Construction.subfieldParameterRestriction F G hFG).w
  let BG := B.pullback v
  let EG := E.pullback v
  let eA' := StagedRecovery.Construction.stagedAbelianRecovery B A.abelian v u w hu eA
  let eD' := StagedRecovery.Construction.stagedAbelianRecovery E A.dual.abelian v u w hu eD
  have : IsMonHom eA'.hom := StagedRecovery.Construction.stagedAbelianRecovery_isMonHom B A.abelian v u w hu eA
  have : IsMonHom eD'.hom := StagedRecovery.Construction.stagedAbelianRecovery_isMonHom E A.dual.abelian v u w hu eD
  let d := StagedProductRecovery.Construction.productFamilyParameterIso v E.scheme B.scheme
  let J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (EG.scheme ⊗ BG.scheme).left := JG.pullback d.hom
  have hq : (Over.homMk u hu : Over.mk w ⟶ Over.mk v) = ParameterLines.Construction.subfieldParameterRestriction F G hFG := rfl
  have hs := StagedProductRecovery.Construction.stagedProductRecovery_square B E A.abelian A.dual.abelian v u w hu eA eD
  have hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD' eA')
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD' eA')
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass d.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf JG)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hs, hq, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    have hclass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterLines.Construction.subfieldParameterRestriction F G hFG ▷ X).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf JG) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := Quotient.sound ⟨hJG⟩
    rw [hclass]
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, c.hom_inv_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  have : Flat u := inferInstance
  have : QuasiCompact u := inferInstance
  have : Surjective u := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ x⟩⟩
  let DG := FpqcMixedPoincareRecovery.Construction.fpqcMixedDescendedDualData A.dual BG u eA' EG eD' J
    (GlobalFunctions.Construction.fieldAbelian_hasUniversalGlobalFunctions BG) hr
  exact ⟨{
    field := G
    abelian := BG
    dual := DG
    sourceRecovery := eA'
    dualRecovery := eD'
    sourceGroup := inferInstanceAs (IsMonHom eA'.hom)
    dualGroup := inferInstanceAs (IsMonHom eD'.hom)
    poincare := FpqcMixedPoincareRecovery.Construction.fpqcMixedDescendedDualData_recovery A.dual BG u eA' EG eD' J
      (GlobalFunctions.Construction.fieldAbelian_hasUniversalGlobalFunctions BG) hr }⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualModel.Construction
