import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient

/-! # Homogeneous Class Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomogeneousClassDescent.Construction

noncomputable section

/-! Homogeneity of an actual Picard class descends along an fppf
parameter cover, by separatedness of the relative Picard sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient.Construction

theorem presheafPullback_square {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Type*)
    {T U V W : C} (q : V ⟶ T) (t : U ⟶ T) (p : W ⟶ U) (v : W ⟶ V)
    (hw : p ≫ t = v ≫ q) (c : P.obj (op T)) :
    P.map p.op (P.map t.op c) = P.map v.op (P.map q.op c) :=
  (P.map_comp_apply t.op p.op c).symm.trans
    ((congrArg (fun m => P.map m.op c) hw).trans (P.map_comp_apply q.op v.op c))

variable {S : Scheme.{u}}

theorem fppfSheaf_restriction_injective
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) {T V : Over S}
    (q : V ⟶ T) [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Function.Injective (F.obj.map q.op) :=
  Presieve.isSeparatedFor_singleton.mp
    (((isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property).isSheafFor _
      (Picard.Homomorphisms.Quotient.Construction.fppf_singleton_over q)).isSeparatedFor

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T V : Over S}
variable (q : V ⟶ T) [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

theorem translationInvariant_of_fppf_pullback (a : T ⟶ A.scheme)
    (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hc : A.TranslationInvariant (q ≫ a) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left c)) :
    A.TranslationInvariant a c := by
  apply fppfSheaf_restriction_injective (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme) q
  have ht := A.translationClass_naturality q a c
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme q
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left c)).trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op V)) ht).trans
      (hc.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme q c).symm))

theorem fppfOverPullback_fst {U : Over S} (t : U ⟶ T) :
    Flat (pullback.fst t q).left ∧ Surjective (pullback.fst t q).left ∧
      LocallyOfFinitePresentation (pullback.fst t q).left := by
  have hs : IsPullback (pullback.fst t q).left (pullback.snd t q).left t.left q.left :=
    (Over.forget S).map_isPullback (IsPullback.of_hasPullback t q)
  exact ⟨MorphismProperty.of_isPullback hs.flip inferInstance,
    MorphismProperty.of_isPullback hs.flip inferInstance,
    MorphismProperty.of_isPullback hs.flip inferInstance⟩

omit [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] in
theorem homogeneousClass_translation_on_square
    (c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op T))
    (hc : A.IsHomogeneousPicardClass V ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map q.op c))
    {U W : Over S} (t : U ⟶ T) (p : W ⟶ U) (v : W ⟶ V) (hw : p ≫ t = v ≫ q)
    (a : U ⟶ A.scheme) :
    A.TranslationInvariant (p ≫ a)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map t.op c)) := by
  let P := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme
  have hp : P.map p.op (P.map t.op c) = P.map v.op (P.map q.op c) :=
    presheafPullback_square P q t p v hw c
  exact Eq.mpr (congrArg (A.TranslationInvariant (p ≫ a)) hp) (hc W v (p ≫ a))

theorem homogeneousClass_of_fppf_pullback
    (c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op T))
    (hc : A.IsHomogeneousPicardClass V ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map q.op c)) :
    A.IsHomogeneousPicardClass T c := by
  intro U t a
  have hp := fppfOverPullback_fst q t
  have : Flat (pullback.fst t q).left := hp.1
  have : Surjective (pullback.fst t q).left := hp.2.1
  have : LocallyOfFinitePresentation (pullback.fst t q).left := hp.2.2
  exact translationInvariant_of_fppf_pullback A (pullback.fst t q) a
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map t.op c)
    (homogeneousClass_translation_on_square A q c hc t (pullback.fst t q) (pullback.snd t q) pullback.condition a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomogeneousClassDescent.Construction
