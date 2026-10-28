import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Fiberwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Multiset.Fintype

/-! # Correspondence Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction

noncomputable section

/-!
Actual finite geometric source fibers and their target multisets. Every
source point contributes once, so distinct kernels with the same target
retain their multiplicity. No degree or volume normalization is introduced.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Enumerate the target values of a finite indexing type, retaining repetitions. -/
def finiteTargetMultiset {I X : Type*} [Finite I] (f : I → X) : Multiset X :=
  letI := Fintype.ofFinite I
  Finset.univ.val.map f

theorem finiteTargetMultiset_reindex {I J X : Type*} [Finite I] [Finite J]
    (e : I ≃ J) (f : I → X) :
    finiteTargetMultiset f = finiteTargetMultiset (f ∘ e.symm) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  change Finset.univ.val.map f = Finset.univ.val.map (f ∘ e.symm)
  have he : (Finset.univ : Finset I).val.map e = (Finset.univ : Finset J).val :=
    congrArg Finset.val (Finset.univ_map_equiv_to_embedding e)
  rw [← he, Multiset.map_map]
  congr 1
  funext i
  simp

theorem finiteTargetMultiset_card {I X : Type*} [Finite I] (f : I → X) :
    (finiteTargetMultiset f).card = Nat.card I := by
  classical
  let := Fintype.ofFinite I
  simp [finiteTargetMultiset, Nat.card_eq_fintype_card]

abbrev SourceFiber {C : Type*} [Category C] {X M P : C} (src : P ⟶ M) (x : X ⟶ M) :=
  { b : X ⟶ P // b ≫ src = x }

def correspondenceFiberMultiset {C : Type*} [Category C] {X M P : C}
    (src dst : P ⟶ M) (x : X ⟶ M) [Finite (SourceFiber src x)] : Multiset (X ⟶ M) :=
  finiteTargetMultiset (fun b : SourceFiber src x => b.val ≫ dst)

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness of the relative parameter gives a finite set of geometric
source-fiber points of its actual scheme over the ground base. -/
theorem totalParameterFiber_finite
    {S : Scheme.{u}} (M : Over S) (P : Over M.left) [IsFinite P.hom]
    {L : Type u} [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S) (x : Over.mk s ⟶ M) :
    Finite (SourceFiber (TotalParameters.Construction.totalParameterSource M P) x) := by
  have hfin : IsFinite (pullback.snd P.hom x.left) := inferInstance
  have : Finite (Over.mk x.left ⟶ P) :=
    @Fiberwise.Construction.finite_points_of_finite_field_baseChange M.left P L inferInstance inferInstance x.left hfin
  exact Finite.of_equiv _ (TotalParameters.Construction.totalParameterFiberLiftEquiv M P (Over.mk s) x).symm

/-- Replacing the geometric source fiber by its classified subgroup
choices preserves the complete multiset, including repeated targets. -/
theorem correspondence_multiset_via_choices
    {S : Scheme.{u}} (M : Over S) (P : Over M.left)
    (F : (Over M.left)ᵒᵖ ⥤ Type (u + 1)) (repr : F.RepresentableBy P)
    (X : Over S) (x : X ⟶ M) (dst : TotalParameters.Construction.totalParameter M P ⟶ M)
    [Finite (SourceFiber (TotalParameters.Construction.totalParameterSource M P) x)] :
    letI : Finite (F.obj (.op (Over.mk x.left))) :=
      Finite.of_equiv _ (TotalParameters.Construction.totalParameterFiberEquiv M P F repr X x)
    correspondenceFiberMultiset (TotalParameters.Construction.totalParameterSource M P) dst x =
      finiteTargetMultiset (fun c : F.obj (.op (Over.mk x.left)) =>
        ((TotalParameters.Construction.totalParameterFiberEquiv M P F repr X x).symm c).val ≫ dst) := by
  let : Finite (F.obj (.op (Over.mk x.left))) :=
    Finite.of_equiv _ (TotalParameters.Construction.totalParameterFiberEquiv M P F repr X x)
  exact finiteTargetMultiset_reindex (TotalParameters.Construction.totalParameterFiberEquiv M P F repr X x)
    (fun b : SourceFiber (TotalParameters.Construction.totalParameterSource M P) x => b.val ≫ dst)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction
