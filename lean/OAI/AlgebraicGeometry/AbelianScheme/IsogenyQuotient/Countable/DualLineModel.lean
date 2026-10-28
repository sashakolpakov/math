import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RecoveredLines
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedProductRecovery

/-! # Dual Line Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualLineModel.Construction

noncomputable section

/-! Full native dual data and any specified actual line on the
original abelian variety admit one common countable algebraically
closed field of definition, preserving both original line classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure CountableDualLineModel {k : Type} [Field k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) where
  model : DualModel.Construction.CountableDualModel A D
  line : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle model.abelian.scheme.left
  recovery : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (Spec.map (CommRingCat.ofHom model.field.subtype))
      A.scheme model.abelian.scheme model.sourceRecovery)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf line) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L

set_option backward.isDefEq.respectTransparency false in
theorem countable_dual_line_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A}
    (M : DualModel.Construction.CountableDualModel A D) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    Nonempty (CountableDualLineModel A D L) := by
  obtain ⟨G, hG, hGa, hFG, J, hJ⟩ :=
    RecoveredLines.Construction.countable_recovered_line_model_exists M.field M.abelian A M.sourceRecovery L
  let : Countable G := hG
  let : IsAlgClosed G := hGa
  let v := (ParameterLines.Construction.subfieldParameter M.field G hFG).hom
  let u := Spec.map (CommRingCat.ofHom G.subtype)
  let w := Spec.map (CommRingCat.ofHom M.field.subtype)
  have hu : u ≫ v = w := (ParameterLines.Construction.subfieldParameterRestriction M.field G hFG).w
  let eA := StagedRecovery.Construction.stagedAbelianRecovery M.abelian A v u w hu M.sourceRecovery
  let eD := StagedRecovery.Construction.stagedAbelianRecovery M.dual.abelian D.abelian v u w hu M.dualRecovery
  let M' : DualModel.Construction.CountableDualModel A D := {
    field := G
    abelian := M.abelian.pullback v
    dual := M.dual.pullback v
    sourceRecovery := eA
    dualRecovery := eD
    sourceGroup := StagedRecovery.Construction.stagedAbelianRecovery_isMonHom M.abelian A v u w hu M.sourceRecovery
    dualGroup := StagedRecovery.Construction.stagedAbelianRecovery_isMonHom M.dual.abelian D.abelian v u w hu M.dualRecovery
    poincare := StagedProductRecovery.Construction.stagedPoincareRecovery_class M.abelian M.dual A D v u w hu
      M.sourceRecovery M.dualRecovery M.poincare }
  exact ⟨⟨M', J, hJ⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualLineModel.Construction
