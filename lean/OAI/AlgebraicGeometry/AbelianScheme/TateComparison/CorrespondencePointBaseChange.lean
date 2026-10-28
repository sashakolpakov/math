import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

/-! # Correspondence Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Base change preserves the actual source-fiber branches and their
endpoint multisets. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S S' T : Scheme.{u}} (p : S' ⟶ S) (c : T ⟶ S')

theorem CorrespondencePointBaseChange.pointBaseChangeEquiv_comp {X Y : Over S} (f : X ⟶ Y)
    (x : Over.mk c ⟶ (Over.pullback p).obj X) :
    FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl Y (x ≫ (Over.pullback p).map f) =
      FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl X x ≫ f := by
  apply Over.OverMorphism.ext
  simp only [FieldPointTransport.pointBaseChangeEquiv_left, Over.comp_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]

variable {X : Over S} (C : Correspondences.EtaleCorrespondence X)

def Correspondences.EtaleCorrespondence.baseChangeFiberEquiv (x : Over.mk c ⟶ (Over.pullback p).obj X) :
    (C.baseChange p).Fiber x ≃
      C.Fiber (FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl X x) :=
  (FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl C.cover).subtypeEquiv (fun z => by
    change z ≫ (Over.pullback p).map C.source = x ↔ _
    rw [← (FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl X).injective.eq_iff,
      CorrespondencePointBaseChange.pointBaseChangeEquiv_comp])

theorem Correspondences.EtaleCorrespondence.baseChangeFiberEquiv_endpoint (x : Over.mk c ⟶ (Over.pullback p).obj X)
    (z : (C.baseChange p).Fiber x) :
    FieldPointTransport.pointBaseChangeEquiv p c (c ≫ p) rfl X ((C.baseChange p).endpoint z) =
      C.endpoint (C.baseChangeFiberEquiv p c x z) :=
  CorrespondencePointBaseChange.pointBaseChangeEquiv_comp p c C.target z.val

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
