import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatCartierEmbeddingIso

/-! # Source Cartier Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceCartierIso.Construction

noncomputable section

/-! Geometric surjectivity of the original Picard image identifies its
actual source-map kernel with the whole Cartier representative. The
finite-flat argument preserves all nilpotent parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B Q : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) [Mono i]
  [IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left] [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    Function.Surjective (i.app (op (Over.mk s))))

include hgeo in
set_option backward.isDefEq.respectTransparency false in
theorem relativePicardImageSourceKernel_cartier_iso
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ c : Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap D f i) ⟶ C.dual.X,
      IsIso c ∧ ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)),
        CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T (x ≫ c)) =
          i.app (op T) (ULift.up (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion (PicardImage.SourceMap.Construction.picardImageSourceMap D f i))) := by
  obtain ⟨c, hc, hv⟩ := SourceKernel.Construction.relativePicardImageSourceKernel_cartier_embedding D f C i p n hn hk
  have : Mono c := hc
  let m := PicardImage.SourceMap.Construction.picardImageSourceMap D f i
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree m ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme m).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme m).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme m).hom := hK.2.2
  have hn' := Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p n hn
  have : IsFinite C.dual.X.hom := C.finite
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n hn' hk
  have hi : IsIso c := by
    apply Finite.FlatCartierEmbeddingIso.Construction.finiteFlatEmbedding_isIso_of_geometric_surjective c
    intro K _ _ s y
    let T := Over.mk s
    obtain ⟨⟨x⟩, hx⟩ := hgeo K s (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T y))
    have hm : x ≫ m = 1 := by
      apply D.representable.homEquiv.injective
      rw [PicardImage.SourceMap.Construction.picardImageSourceMap_value, hx, D.origin, Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one]
      exact (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f T _).symm.trans
        (Parameter.CharacterPullback.Construction.parameterCharacterPicardHom_pullback_one f T (C.sectionEquiv T y))
    let z := Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift m x hm
    refine ⟨z, ?_⟩
    apply (C.sectionEquiv T).injective
    apply Relative.CharacterPicardInjection.Construction.parameterCharacterPicardHom_injective f C n hn' hk T
    have hv' := hv T z
    rw [Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion] at hv'
    exact hv'.trans hx
  exact ⟨c, hi, hv⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceCartierIso.Construction
