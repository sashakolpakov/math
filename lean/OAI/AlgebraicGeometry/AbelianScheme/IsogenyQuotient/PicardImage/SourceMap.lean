import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalPicardSheafMap
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity

/-! # Source Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap.Construction

noncomputable section

/-! The original source dual represents Picard pullback from an abelian
image. This constructs the actual morphism from that image to the source
dual without assuming a dual for the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

universe u
section General
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)

def picardImageSourceMap : C ⟶ D.abelian :=
  D.representable.homEquiv.symm
    ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op C) (i.app (op C) (ULift.up (𝟙 C))))

theorem picardImageSourceMap_value {T : Over S} (x : T ⟶ C) :
    D.representable.homEquiv (x ≫ picardImageSourceMap D f i) =
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) (i.app (op T) (ULift.up x)) := by
  rw [D.representable.homEquiv_comp, picardImageSourceMap, Equiv.apply_symm_apply]
  let p := i ≫ (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom
  have h := (congrArg (fun t : (uliftYoneda.{u + 1}.obj C).obj (op C) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T) => t (ULift.up (𝟙 C))) (p.naturality x.op)).symm
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.map x.op (p.app (op C) (ULift.up (𝟙 C))) =
    p.app (op T) (ULift.up (x ≫ 𝟙 C)) at h
  rw [Category.comp_id] at h
  exact h

variable [GrpObj C]

theorem picardImageSourceMap_one
    (hi : ∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ C)) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B T)
    (T : Over S) : (1 : T ⟶ C) ≫ picardImageSourceMap D f i = 1 := by
  apply D.representable.homEquiv.injective
  rw [picardImageSourceMap_value, hi, D.origin]
  exact Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_trivial A B f T

variable (q : B ⟶ C)
  (m : uliftYoneda.{u + 1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = m)
  (φ : A ⟶ D.abelian)
  (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd D.abelian A) (fst D.abelian A)
    (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare))
  (hsource : uliftYoneda.map f ≫ m ≫ (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom =
    Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap φ (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) Dv)

include hfac hsource in
omit [GrpObj C] in
theorem picardImageSourceMap_factorization : f ≫ q ≫ picardImageSourceMap D f i = φ := by
  apply D.representable.homEquiv.injective
  rw [← Category.assoc, picardImageSourceMap_value]
  have he : uliftYoneda.map (f ≫ q) ≫ i ≫ (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom =
      Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap φ (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) Dv := by
    rw [Functor.map_comp, Category.assoc, ← Category.assoc (uliftYoneda.map q), hfac]
    exact hsource
  have hv := congrArg (fun t : uliftYoneda.{u + 1}.obj A ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj =>
    t.app (op A) (ULift.up (𝟙 A))) he
  change (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op A)
      (i.app (op A) (ULift.up ((𝟙 A) ≫ f ≫ q))) =
    (Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap φ (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) Dv).app (op A) (ULift.up (𝟙 A)) at hv
  rw [Category.id_comp] at hv
  refine hv.trans ?_
  change (ProductPicard.SheafMap.Construction.productNativePicardSheafMap _ _ _).app (op A) (ULift.up (𝟙 A)) = _
  rw [Poincare.PicardSheafValue.Construction.poincareFamily_nativePicard_value, Category.id_comp]

end General

variable {k : Type u} [Field k] {A B C : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj C]
  [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)

theorem picardImageSourceMap_isMonHom
    (hi : ∀ T : Over (Spec (.of k)),
      i.app (op T) (ULift.up (1 : T ⟶ C)) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B T) :
    IsMonHom (picardImageSourceMap D f i) := by
  apply IsogenyQuotient.Field.GroupRigidity.Construction.pointed_isMonHom_over_field C D.abelian
  have h := picardImageSourceMap_one D f i hi (𝟙_ (Over (Spec (.of k))))
  simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap.Construction
