import OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous

/-! # Homogeneous Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison

noncomputable section

/-! Exact comparison of the PoincareBundle and shared homogeneous Picard sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeComparison

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

omit [GrpObj A] in
theorem mapped_class {T U : Over S} (f : U ⟶ T)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q) =
      Line.Comparison.Bundle.classEquiv (U ⊗ A).left ((Functor.relativePicardPresheaf A).map f.op q) :=
  (Line.Comparison.Bundle.classEquiv_pullback ((Functor.familySchemeFunctor A).map f) q).symm

theorem translated_class {T U : Over S} (f : U ⟶ T) (a : U ⟶ A)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q)) =
      Line.Comparison.Bundle.classEquiv (U ⊗ A).left
        (Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left
          ((Functor.relativePicardPresheaf A).map f.op q)) := by
  rw [mapped_class]
  exact (Line.Comparison.Bundle.classEquiv_pullback (Homogeneous.translation A a).left _).symm

omit [GrpObj A] in
theorem base_section {T U : Over S} (f : U ⟶ T)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q)) =
      (RelativeComparison.sheafIso A).hom.hom.app (op U) ((Functor.toRelativePicard A).app (op U)
        ((Functor.relativePicardPresheaf A).map f.op q)) :=
  (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)) (mapped_class A f q)).trans
    (RelativeComparison.section_comparison A _).symm

theorem translated_section {T U : Over S} (f : U ⟶ T) (a : U ⟶ A)
    (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left
          ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q))) =
      (RelativeComparison.sheafIso A).hom.hom.app (op U) ((Functor.toRelativePicard A).app (op U)
        (Line.Bundles.LineBundleClass.pullback (Homogeneous.translation A a).left
          ((Functor.relativePicardPresheaf A).map f.op q))) :=
  (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U)) (translated_class A f a q)).trans
    (RelativeComparison.section_comparison A _).symm

/-- Homogeneity has exactly the same geometric meaning in the two APIs. -/
theorem homogeneous_iff {T : Over S} (q : (Functor.relativePicardPresheaf A).obj (op T)) :
    Homogeneous.IsHomogeneous A T q ↔
      Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A T (Line.Comparison.Bundle.classEquiv (T ⊗ A).left q) := by
  constructor
  · intro h U f a
    rw [translated_section, base_section]
    exact congrArg ((RelativeComparison.sheafIso A).hom.hom.app (op U)) (h U f a)
  · intro h U f a
    have hh := h U f a
    rw [translated_section, base_section] at hh
    exact (ConcreteCategory.bijective_of_isIso ((RelativeComparison.sheafIso A).hom.hom.app (op U))).1 hh

/-- The class comparison restricts to actual homogeneous classes. -/
def homogeneousClassEquiv (T : Over S) :
    (Homogeneous.homogeneousPresheaf A).obj (op T) ≃
      (Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (op T) :=
  Equiv.subtypeEquiv (Line.Comparison.Bundle.classEquiv (T ⊗ A).left) (homogeneous_iff A)

/-- The restricted comparison is natural on every test scheme. -/
def homogeneousPresheafIso : Homogeneous.homogeneousPresheaf A ≅
    Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A :=
  NatIso.ofComponents (fun T => (homogeneousClassEquiv A T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact Line.Comparison.Bundle.classEquiv_pullback ((Functor.familySchemeFunctor A).map f.unop) q.val)

/-- The actual represented homogeneous Picard sheaves are canonically isomorphic. -/
def homogeneousSheafIso : Homogeneous.homogeneousSheaf A ≅
    Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso (homogeneousPresheafIso A)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison
