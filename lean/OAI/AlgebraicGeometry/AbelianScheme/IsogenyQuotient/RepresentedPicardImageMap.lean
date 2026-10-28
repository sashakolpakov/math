import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Represented Picard Image Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedPicardImageMap.Construction

noncomputable section

/-! A represented target Picard sheaf turns its actual image map
into a scheme morphism, preserving its full pointwise formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {B Q : Over S} [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)

def representedPicardImageMap : Q ⟶ D.abelian :=
  D.representable.homEquiv.symm (i.app (op Q) (ULift.up (𝟙 Q)))

theorem representedPicardImageMap_value {T : Over S} (x : T ⟶ Q) :
    D.representable.homEquiv (x ≫ representedPicardImageMap D i) = i.app (op T) (ULift.up x) := by
  rw [D.representable.homEquiv_comp, representedPicardImageMap, Equiv.apply_symm_apply]
  have h := (congrArg (fun b : (uliftYoneda.{u + 1}.obj Q).obj (op Q) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) => b (ULift.up (𝟙 Q))) (i.naturality x.op)).symm
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map x.op (i.app (op Q) (ULift.up (𝟙 Q))) =
    i.app (op T) (ULift.up (x ≫ 𝟙 Q)) at h
  rwa [Category.comp_id] at h

theorem representedPicardImageMap_mono [Mono i] : Mono (representedPicardImageMap D i) := by
  constructor
  intro T x y h
  have hinj : Function.Injective (i.app (op T)) := (CategoryTheory.mono_iff_injective _).mp inferInstance
  apply ULift.up_injective
  apply hinj
  rw [← representedPicardImageMap_value, ← representedPicardImageMap_value, h]

theorem representedPicardImageMap_isIso_sheaf [IsIso (representedPicardImageMap D i)] : IsIso i := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply ULift.ext
    apply (cancel_mono (representedPicardImageMap D i)).mp
    apply D.representable.homEquiv.injective
    exact (representedPicardImageMap_value D i x.down).trans
      (h.trans (representedPicardImageMap_value D i y.down).symm)
  · intro y
    refine ⟨ULift.up (D.representable.homEquiv.symm y ≫ inv (representedPicardImageMap D i)), ?_⟩
    rw [← representedPicardImageMap_value, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedPicardImageMap.Construction
