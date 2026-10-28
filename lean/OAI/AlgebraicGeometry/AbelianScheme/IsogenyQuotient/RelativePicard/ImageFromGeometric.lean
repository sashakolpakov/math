import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceCartierIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageSheafIso

/-! # Image From Geometric -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromGeometric.Construction

noncomputable section

/-! Geometric Picard-image surjectivity, the actual finite-flat source
map, and the relative Cartier kernel theorem imply full relative
Picard representability on every parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B Q : Over S} [GrpObj A] [GrpObj B] [GrpObj Q] [IsCommMonObj Q]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj) [Mono i]
  (F : ∀ T : Over S, (T ⟶ Q) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
  (hF : ∀ (T : Over S) (x : T ⟶ Q), F T x = i.app (op T) (ULift.up x))
  [IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left] [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  [Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    Function.Surjective (i.app (op (Over.mk s))))

include D C F hF hgeo in
theorem relativePicardImage_isIso_of_geometric_sections
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) : IsIso i := by
  obtain ⟨c, hc, hv⟩ := SourceCartierIso.Construction.relativePicardImageSourceKernel_cartier_iso D f C i hgeo p n hn hk
  have : IsIso c := hc
  exact ImageSheafIso.Construction.relativePicardImage_isIso_of_character_iso D f C i F hF
    (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (PicardImage.SourceMap.Construction.picardImageSourceMap D f i)) c hv p n hn hk

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromGeometric.Construction
