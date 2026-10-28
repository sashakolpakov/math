import OAI.AlgebraicGeometry.SheafCohomology.Projective.SheafificationTensorAssociator
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorTripleNaturality

/-! # Local Tensor Section Coherence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalTensorSectionCoherence

noncomputable section

/-! Associators on actual pure tensor sections over arbitrary opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance localTensorCoherenceMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X
local instance localTensorCoherenceSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem associator_tensorSection {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (α_ M N P).hom.val.app (op U)
      (TensorSections.tensorSection (M ⊗ N) P U (TensorSections.tensorSection M N U x y) z) =
        TensorSections.tensorSection M (N ⊗ P) U x (TensorSections.tensorSection N P U y z) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let cM := Invertible.Scheme.Modules.sheafifyValIso M
  let cN := Invertible.Scheme.Modules.sheafifyValIso N
  let cP := Invertible.Scheme.Modules.sheafifyValIso P
  have h := TensorTripleNaturality.associator_tensorSection_transport cM.hom cN.hom cP.hom U
    ((adj.unit.app M.val).app (op U) x) ((adj.unit.app N.val).app (op U) y)
    ((adj.unit.app P.val).app (op U) z)
    (SheafificationTensorAssociator.sheafification_associator_tensorSection M.val N.val P.val U x y z)
  simpa only [cM, cN, cP, adj,
    TensorFrameSections.sheafifyValIso_hom_unit_apply] using h

theorem associator_inv_tensorSection {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (α_ M N P).inv.val.app (op U)
      (TensorSections.tensorSection M (N ⊗ P) U x (TensorSections.tensorSection N P U y z)) =
        TensorSections.tensorSection (M ⊗ N) P U (TensorSections.tensorSection M N U x y) z := by
  have h := congrArg (fun t => (α_ M N P).inv.val.app (op U) t)
    (associator_tensorSection M N P U x y z)
  exact h.symm.trans (SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT (α_ M N P).symm (op U) _)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalTensorSectionCoherence
