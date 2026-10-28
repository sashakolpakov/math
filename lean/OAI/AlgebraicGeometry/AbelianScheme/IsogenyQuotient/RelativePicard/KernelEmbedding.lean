import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicardKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterMap

/-! # Kernel Embedding -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.KernelEmbedding.Construction

noncomputable section

/-! Any represented subfunctor of the relative Picard pullback kernel
embeds in the actual Cartier dual, with its original character-line value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B K : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (j : uliftYoneda.{u + 1}.obj K ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) [Mono j]
  (hj : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f K (j.app (op K) (ULift.up (𝟙 K))) = 1)

include hj in
theorem relativePicardKernel_exists_cartier_embedding
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ c : K ⟶ C.dual.X, Mono c ∧ ∀ (T : Over S) (x : T ⟶ K),
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T (x ≫ c)) = j.app (op T) (ULift.up x) := by
  obtain ⟨a, ha, _⟩ := Relative.CartierPicardKernel.Construction.relativePicardPullbackKernel_existsUnique_cartierPoint f C p n hn hk K
    (j.app (op K) (ULift.up (𝟙 K))) hj
  let χ := C.sectionEquiv K a
  let c := RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap f C χ
  exact ⟨c, RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_mono f C j χ ha,
    fun T x => RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f C j χ ha x⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.KernelEmbedding.Construction
