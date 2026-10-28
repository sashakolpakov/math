import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.KernelEmbedding
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperSubfunctorFinite
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps

/-! # Source Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceKernel.Construction

noncomputable section

/-! An actual Picard image embeds its source-map kernel into the Cartier
dual of the original isogeny kernel. Properness then proves the source
map finite over the entire characteristic-zero base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps.Construction

universe u
variable {S : Scheme.{u}} {A B Q : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) [Mono i]

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [Mono i] in
theorem picardImageSourceKernel_native_zero {T : Over S} (x : T ⟶ Q)
    (hx : x ≫ PicardImage.SourceMap.Construction.picardImageSourceMap D f i = 1) :
    UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T (i.app (op T) (ULift.up x)) = 1 := by
  rw [UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply, ← PicardImage.SourceMap.Construction.picardImageSourceMap_value, hx, D.origin]
  exact Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one A T

theorem relativePicardImageSourceKernel_cartier_embedding
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ c : Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap D f i) ⟶ C.dual.X,
      Mono c ∧ ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)),
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T (x ≫ c)) =
          i.app (op T) (ULift.up (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion (PicardImage.SourceMap.Construction.picardImageSourceMap D f i))) := by
  let g := PicardImage.SourceMap.Construction.picardImageSourceMap D f i
  let j := uliftYoneda.{u + 1}.map (Picard.Homomorphisms.Kernel.Construction.kernelInclusion g) ≫ i
  have hj : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)
      (j.app (op (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)) (ULift.up (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)))) = 1 := by
    change UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)
      (i.app (op (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)) (ULift.up ((𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme g)) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion g))) = 1
    rw [Category.id_comp]
    exact picardImageSourceKernel_native_zero D f i (Picard.Homomorphisms.Kernel.Construction.kernelInclusion g) (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp g)
  exact KernelEmbedding.Construction.relativePicardKernel_exists_cartier_embedding f C j hj p n hn hk

include C in
theorem relativePicardImageSourceMap_finite
    [GrpObj Q] [IsProper Q.hom] [IsMonHom (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)]
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left := by
  obtain ⟨c, hc, _⟩ := relativePicardImageSourceKernel_cartier_embedding D f C i p n hn hk
  have : Mono c := hc
  have : IsFinite C.dual.X.hom := C.finite
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)).hom :=
    ProperSubfunctorFinite.Construction.proper_subfunctor_of_finite_isFinite c
  exact Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceKernel.Construction
