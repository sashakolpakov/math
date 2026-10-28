import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteOverField
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Opposite Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The opposite annihilator is the actual scheme kernel of character
restriction. The source group law, finite locally free model over a field,
closed inclusion, and all-test character condition are proved here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj IsMulCommutative

universe u

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}
variable (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H) (i : H ⟶ G)

def CartierModel.Construction.CartierCoordinates.annihilatorGroup : Grp (Over (Spec R)) :=
  @Grp.mk _ _ _ (Picard.PoincareBundle.Kernel.Scheme.kernelObject (P.restriction Q i).hom.hom)
    (Picard.PoincareBundle.Kernel.Scheme.kernelGroup (P.restriction Q i).hom.hom)

def CartierModel.Construction.CartierCoordinates.annihilatorInclusion : P.annihilatorGroup Q i ⟶ P.dualGroup :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusionAsGroup (P.restriction Q i).hom.hom

theorem CartierModel.Construction.CartierCoordinates.annihilatorInclusion_eq :
    (P.annihilatorInclusion Q i).hom.hom =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (P.restriction Q i).hom.hom :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusionAsGroup_hom _

instance CartierModel.Construction.CartierCoordinates.annihilatorGroup_commutative : IsCommMonObj (P.annihilatorGroup Q i).X :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative (P.restriction Q i).hom.hom

instance CartierModel.Construction.CartierCoordinates.restriction_finite : IsFinite (P.restriction Q i).hom.hom.left := by
  let d := (P.restriction Q i).hom.hom
  have : IsFinite (d.left ≫ Q.dualGroup.X.hom) := (congrArg IsFinite d.w).mpr inferInstance
  exact IsFinite.of_comp d.left Q.dualGroup.X.hom

instance CartierModel.Construction.CartierCoordinates.annihilatorGroup_finite : IsFinite (P.annihilatorGroup Q i).X.hom :=
  Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (P.restriction Q i).hom.hom

instance CartierModel.Construction.CartierCoordinates.annihilatorInclusion_mono : Mono (P.annihilatorInclusion Q i).hom.hom := by
  constructor
  intro T x y h
  apply (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (P.restriction Q i).hom.hom T).injective
  apply Subtype.ext
  exact (congrArg (fun f => x ≫ f) (P.annihilatorInclusion_eq Q i).symm).trans
    (h.trans (congrArg (fun f => y ≫ f) (P.annihilatorInclusion_eq Q i)))

theorem CartierModel.Construction.CartierCoordinates.annihilatorInclusion_closed :
    IsClosedImmersion (P.annihilatorInclusion Q i).hom.hom.left :=
  OrdinaryBlocks.Construction.closedSubgroupOfFiniteMono (P.annihilatorInclusion Q i).hom.hom

/-- The kernel condition is exactly triviality of the restricted
character, with no restriction to reduced or field-valued tests. -/
theorem CartierModel.Construction.CartierCoordinates.annihilator_condition (T : Over (Spec R)) (x : T ⟶ P.dualGroup.X) :
    x ≫ (P.restriction Q i).hom.hom = 1 ↔
      Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T x = 1 := by
  constructor
  · intro hx
    exact (P.restriction_on_characters Q i T x).symm.trans
      ((congrArg (Q.pointsEquiv T) hx).trans (Q.pointsEquiv T).map_one)
  · intro hx
    apply (Q.pointsEquiv T).injective
    exact (P.restriction_on_characters Q i T x).trans
      (hx.trans (Q.pointsEquiv T).map_one.symm)

/-- A character annihilates the chosen subgroup exactly when its point
factors uniquely through the constructed opposite-kernel scheme. -/
theorem CartierModel.Construction.CartierCoordinates.annihilator_universal (T : Over (Spec R)) (x : T ⟶ P.dualGroup.X) :
    (Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T x = 1) ↔
      ∃! y : T ⟶ (P.annihilatorGroup Q i).X, y ≫ (P.annihilatorInclusion Q i).hom.hom = x := by
  constructor
  · intro hx
    let y := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (P.restriction Q i).hom.hom T).symm
      ⟨x, (P.annihilator_condition Q i T x).mpr hx⟩
    have hy : y ≫ (P.annihilatorInclusion Q i).hom.hom = x := by
      rw [P.annihilatorInclusion_eq Q i]
      exact congrArg Subtype.val
        ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (P.restriction Q i).hom.hom T).apply_symm_apply _)
    refine ⟨y, hy, ?_⟩
    intro z hz
    apply (cancel_mono (P.annihilatorInclusion Q i).hom.hom).mp
    exact hz.trans hy.symm
  · rintro ⟨y, hy, _⟩
    apply (P.annihilator_condition Q i T x).mp
    have h := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (P.restriction Q i).hom.hom T y).property
    change (y ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (P.restriction Q i).hom.hom) ≫
      (P.restriction Q i).hom.hom = 1 at h
    exact (congrArg (fun z => z ≫ (P.restriction Q i).hom.hom)
      (hy.symm.trans (congrArg (fun f => y ≫ f) (P.annihilatorInclusion_eq Q i)))).trans h

theorem CartierModel.Construction.CartierCoordinates.annihilatorGroup_finiteLocallyFree_overField
    {K : Type u} [Field K] {G H : Grp (Over (Spec (.of K)))}
    (P : CartierModel.Construction.CartierCoordinates (.of K) G) (Q : CartierModel.Construction.CartierCoordinates (.of K) H) (i : H ⟶ G) :
    IsFinite (P.annihilatorGroup Q i).X.hom ∧
      Flat (P.annihilatorGroup Q i).X.hom ∧
      LocallyOfFinitePresentation (P.annihilatorGroup Q i).X.hom :=
  ⟨inferInstance, FiniteOverField.Construction.finiteOverField_finiteLocallyFree (P.annihilatorGroup Q i).X.hom⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
