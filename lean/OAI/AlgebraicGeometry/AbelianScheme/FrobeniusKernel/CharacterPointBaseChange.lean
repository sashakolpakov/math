import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCanonicalBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceCartierRepresentation

/-! # Character Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPointBaseChange.Construction

noncomputable section

section

/-! The native Cartier base-change square retains the original HilbertConstruction
dual data and its Picard-derived group on the pulled-back source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {k k' : Type} [Field k] [Field k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (s : Spec (.of k') ⟶ Spec (.of k))
variable (f : A.abelian.scheme ⟶ A.abelian.scheme) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (f' : (Over.pullback s).obj A.abelian.scheme ⟶ (Over.pullback s).obj A.abelian.scheme)
variable [IsMonHom f'] (hf : f' = (Over.pullback s).map f)
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k')) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

omit [IsMonHom f] in
theorem originalCartierPicardChangedMap :
    CartierPicardBaseChange.Construction.nativeCartierPicardChangedMap s f f' hf C' (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup =
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
      letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
      ReferenceCartierRepresentation.Construction.originalCartierPullbackMap A.dual s f' C' := by
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
  exact (PicardCanonicalBaseChange.Construction.nativeCartierPicardChangedMap_canonical s f f' hf C' (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)).trans
    (ReferenceCartierRepresentation.Construction.originalCartierRepresentation_baseChange A.dual s f' C')

theorem originalCartierPicard_baseChange
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
    (CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C').hom.hom ≫
        ReferenceCartierRepresentation.Construction.originalCartierPullbackMap A.dual s f' C' =
      (Over.pullback s).map (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup C) :=
  (congrArg (fun z => (CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C').hom.hom ≫ z)
    (originalCartierPicardChangedMap A s f f' hf C')).symm.trans
      (CartierPicardBaseChange.Construction.nativeCartierPicard_baseChange_along s f f' hf C C' (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup)

end

/-! Original polarization character points commute with source base
change through their actual descended line and full dual point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (s : Spec (.of k') ⟶ Spec (.of k))
variable (f : A.abelian.scheme ⟶ A.abelian.scheme) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (f' : (Over.pullback s).obj A.abelian.scheme ⟶ (Over.pullback s).obj A.abelian.scheme)
variable [IsMonHom f'] (hf : f' = (Over.pullback s).map f)
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k')) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem originalCartierCharacterPoint_baseChange (n : ℕ) (Q : Over (Spec (.of k')))
    (y : ((A.pullback s).abelian.torsionFunctor n).obj (.op Q))
    (d : (Over.map s).obj Q ⟶ C.dual.X)
    (hd : d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup C =
      PolarizationPointBaseChange.Construction.originalNativePolarizationImage A n ((Over.map s).obj Q) (A.abelian.torsionBaseChangeEquiv s Q n y)) :
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
    letI := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
    (((Over.mapPullbackAdj s).homEquiv Q C.dual.X d) ≫
      (CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C').hom.hom) ≫
        ReferenceCartierRepresentation.Construction.originalCartierPullbackMap A.dual s f' C' =
      PolarizationPointBaseChange.Construction.originalNativePolarizationImage (A.pullback s) n Q y := by
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_affine s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_flat s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_surjective s f f' hf
  let := CartierPicardBaseChange.Construction.nativeChangedCoverAlong_presentation s f f' hf
  let dp := (Over.mapPullbackAdj s).homEquiv Q C.dual.X d
  let c := CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C'
  let p := CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup C
  apply (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian s Q).injective
  have hc := (Category.assoc dp c.hom.hom _).trans
    (congrArg (fun z => dp ≫ z) (originalCartierPicard_baseChange A s f f' hf C' C))
  have hp := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm dp p
  have hd0 := ((Over.mapPullbackAdj s).homEquiv Q C.dual.X).symm_apply_apply d
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian s Q) hc).trans
    (hp.trans ((congrArg (fun z => z ≫ p) hd0).trans
      (hd.trans (PolarizationPointBaseChange.Construction.originalNativePolarizationPoint_baseChange A n s Q y).symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPointBaseChange.Construction
