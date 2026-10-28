import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphProjectionBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismLocus

/-! # Family Graph Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyGraphOpen.Hom

noncomputable section

/-! The graph locus of an actual native Hilbert family over a locally
noetherian parameter scheme is open, with its exact criterion on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom]

theorem nativeGraphTarget_isProper (B : Over S) :
    IsProper (Hilbert.Functor.ambientProjection X B) := by
  change IsProper (prod.fst : B ⨯ X ⟶ B).left
  rw [← Over.prodLeftIsoPullback_hom_fst]
  infer_instance

def nativeFamilyGraphOpen {B : Over S} (F : Hilbert.Functor.Family (X ⨯ Y) B) : B.left.Opens := by
  let := nativeGraphTarget_isProper X B
  exact Proper.RelativeIsomorphismOpen.properRelativeIsomorphismOpen (GraphLocus.Hom.subschemeProjection X Y F.val).left
    (Hilbert.Functor.ambientProjection X B)

theorem nativeFamilyGraphOpen_baseChange_iff_range {T B : Over S}
    [IsLocallyNoetherian B.left] (F : Hilbert.Functor.Family (X ⨯ Y) B) (a : T ⟶ B) :
    IsIso (GraphLocus.Hom.subschemeProjection X Y (Hilbert.Functor.pullbackFamily (X ⨯ Y) a F).val) ↔
      Set.range a.left ⊆ (nativeFamilyGraphOpen X Y F : Set B.left) := by
  let q := Hilbert.Functor.ambientProjection X B
  let f := (GraphLocus.Hom.subschemeProjection X Y F.val).left
  let : IsProper q := nativeGraphTarget_isProper X B
  let : IsLocallyNoetherian (Hilbert.Functor.ambient X B) := LocallyOfFiniteType.isLocallyNoetherian q
  have hc : f ≫ q = Hilbert.Functor.familyProjection (X ⨯ Y) F.val :=
    GraphProjectionBaseChange.Hom.subschemeProjection_familyProjection X Y F.val
  have hp : IsProper (f ≫ q) := hc.symm ▸ F.property.2.1
  let := hp
  let : IsProper f := IsProper.of_comp f q
  let : Flat (f ≫ q) := hc.symm ▸ F.property.1
  exact (GraphProjectionBaseChange.Hom.nativeGraphProjection_baseChange_isIso_iff X Y a F.val).symm.trans
    (Proper.RelativeIsomorphismLocus.properRelative_isIso_baseChange_iff_range f q a.left)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyGraphOpen.Hom
