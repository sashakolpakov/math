import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.ParameterLines
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedRecovery

/-! # Recovered Lines -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RecoveredLines.Construction

noncomputable section

/-! An arbitrary actual line on a recovered abelian variety descends
after a countable algebraically closed enlargement, with its exact
original class recovered on the original variety. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem countable_recovered_line_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    (F : Subfield k) [Countable F] {g : ℕ}
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of F))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (e : A.scheme ≅ (B.pullback (Spec.map (CommRingCat.ofHom F.subtype))).scheme)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    ∃ G : Subfield k, Countable G ∧ IsAlgClosed G ∧ ∃ hFG : F ≤ G,
      ∃ J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.pullback (ParameterLines.Construction.subfieldParameter F G hFG).hom).scheme.left,
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
          (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (Spec.map (CommRingCat.ofHom G.subtype)) A.scheme
            (B.pullback (ParameterLines.Construction.subfieldParameter F G hFG).hom).scheme
            (StagedRecovery.Construction.stagedAbelianRecovery B A (ParameterLines.Construction.subfieldParameter F G hFG).hom
              (Spec.map (CommRingCat.ofHom G.subtype)) (Spec.map (CommRingCat.ofHom F.subtype))
              (ParameterLines.Construction.subfieldParameterRestriction F G hFG).w e))
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  let w := Spec.map (CommRingCat.ofHom F.subtype)
  let c := StagedRecovery.Construction.recoveredFamilyParameterIso w B.scheme e
  let L' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F k ⊗ B.scheme).left := L.pullback c.inv
  obtain ⟨G, hG, hGa, hFG, JG, ⟨hJG⟩⟩ := ParameterLines.Construction.countable_parameter_line_model_exists F B.scheme L'
  let v := (ParameterLines.Construction.subfieldParameter F G hFG).hom
  let u := Spec.map (CommRingCat.ofHom G.subtype)
  have hu : u ≫ v = w := (ParameterLines.Construction.subfieldParameterRestriction F G hFG).w
  let d := pullbackSymmetry B.scheme.hom v
  let J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.pullback v).scheme.left := JG.pullback d.hom
  refine ⟨G, hG, hGa, hFG, J, ?_⟩
  have hq : (Over.homMk u hu : Over.mk w ⟶ Over.mk v) = ParameterLines.Construction.subfieldParameterRestriction F G hFG := rfl
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme (B.pullback v).scheme
        (StagedRecovery.Construction.stagedAbelianRecovery B A v u w hu e))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass d.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf JG)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, StagedRecovery.Construction.stagedLineRecovery_square, hq, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have hclass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterLines.Construction.subfieldParameterRestriction F G hFG ▷ B.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf JG) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L' := Quotient.sound ⟨hJG⟩
  rw [hclass]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, c.hom_inv_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RecoveredLines.Construction
