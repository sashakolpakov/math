import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages

/-! # Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Source.Construction

noncomputable section

/-! The exact source-polarization factorization makes the constructed
map from the abelian Picard image to the original source dual finite,
flat and surjective. No dimension comparison or quotient dual is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] {A B C : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj C]
  [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f] [Surjective f.left]
  (q : B ⟶ C) [Surjective q.left]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hi : ∀ T : Over (Spec (.of k)),
    i.app (op T) (ULift.up (1 : T ⟶ C)) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B T)
  (φ : A ⟶ D.abelian) [IsFinite φ.left] [Surjective φ.left]
  (h : f ≫ q ≫ SourceMap.Construction.picardImageSourceMap D f i = φ)

include hi h in
theorem picardImageSourceMap_finite_flat_surjective :
    IsFinite (SourceMap.Construction.picardImageSourceMap D f i).left ∧ Flat (SourceMap.Construction.picardImageSourceMap D f i).left ∧
      Surjective (SourceMap.Construction.picardImageSourceMap D f i).left := by
  let g := SourceMap.Construction.picardImageSourceMap D f i
  have : IsMonHom g := SourceMap.Construction.picardImageSourceMap_isMonHom D f i hi
  have : IsProper (g.left ≫ D.abelian.hom) := by rw [g.w]; infer_instance
  have : IsProper g.left := IsProper.of_comp g.left D.abelian.hom
  have he : (f.left ≫ q.left) ≫ g.left = φ.left :=
    (Category.assoc f.left q.left g.left).trans (congrArg Over.Hom.left h)
  have : IsFinite ((f.left ≫ q.left) ≫ g.left) := by rw [he]; infer_instance
  have : Surjective ((f.left ≫ q.left) ≫ g.left) := by rw [he]; infer_instance
  have : IsFinite g.left := CartierDuality.FiniteImages.Construction.Schemes.finite_of_proper_of_surjective_comp (f.left ≫ q.left) g.left
  have : Surjective g.left := Surjective.of_comp (f.left ≫ q.left) g.left
  exact ⟨inferInstance, Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat g, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Source.Construction
