import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentationMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism

/-! # Cartier Picard Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction

noncomputable section

section

/-! Arbitrary native Cartier representatives retain the canonical
character-line map after change of the source base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup CharacterLineBaseChange.Construction.parameterChangedCover_affine
  CharacterLineBaseChange.Construction.parameterChangedCover_flat CharacterLineBaseChange.Construction.parameterChangedCover_surjective CharacterPicardBaseChange.Construction.parameterChangedCover_presentation

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f))))

def nativeCartierBaseChangeMap : (C.baseChange s).dual ⟶ C'.dual :=
  (C.baseChange s).dualMap C' (CharacterBaseChangeValues.Construction.nativeKernelBaseChangeInverseGroup s f)

theorem nativeCartierBaseChangeMap_character (Q : Over S') (z : Q ⟶ (C.baseChange s).dual.X) :
    C'.sectionEquiv Q (z ≫ (nativeCartierBaseChangeMap s f C C').hom.hom) =
      CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q
        (C.sectionEquiv ((Over.map s).obj Q) (C.baseChangeOriginalPoint s Q z)) :=
  ((C.baseChange s).dualMap_character C' (CharacterBaseChangeValues.Construction.nativeKernelBaseChangeInverseGroup s f) Q z).trans
    (congrArg (CartierDuality.RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (CharacterBaseChangeValues.Construction.nativeKernelBaseChangeInverseGroup s f) Q)
      (C.baseChange_section s Q z))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

theorem nativeCartierPicard_baseChange_points (Q : Over S') (z : Q ⟶ (C.baseChange s).dual.X) :
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q
      (z ≫ (nativeCartierBaseChangeMap s f C C').hom.hom ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((Over.pullback s).map f) (D.pullback s) C') =
      C.baseChangeOriginalPoint s Q z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C := by
  have hc := nativeCartierBaseChangeMap_character s f C C' Q z
  have hp := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply ((Over.pullback s).map f) (D.pullback s) C' Q
    (z ≫ (nativeCartierBaseChangeMap s f C C').hom.hom)
  have hn := (congrArg (fun χ => CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((Over.pullback s).map f) Q χ
    (D.pullback s)) hc)
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q)
      ((Category.assoc _ _ _).symm.trans (hp.trans hn))).trans
    ((CharacterPicardBaseChange.Construction.parameterCharacterDualPoint_baseChange s Q f
      (C.sectionEquiv ((Over.map s).obj Q) (C.baseChangeOriginalPoint s Q z)) D).trans
      (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C ((Over.map s).obj Q) (C.baseChangeOriginalPoint s Q z)).symm)

theorem nativeCartierPicard_baseChange :
    (nativeCartierBaseChangeMap s f C C').hom.hom ≫
        CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((Over.pullback s).map f) (D.pullback s) C' =
      (Over.pullback s).map (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  apply (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s (C.baseChange s).dual.X).injective
  have hp := nativeCartierPicard_baseChange_points s f C C' D (C.baseChange s).dual.X (𝟙 _)
  have hr := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm
    (𝟙 (C.baseChange s).dual.X) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C)
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s (C.baseChange s).dual.X)
      (Category.id_comp _).symm).trans (hp.trans hr.symm)

end

section

/-! The native base-change square is insensitive to writing a pulled
cover by an equal morphism, in particular the literal multiplication map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup CharacterLineBaseChange.Construction.parameterChangedCover_affine
  CharacterLineBaseChange.Construction.parameterChangedCover_flat CharacterLineBaseChange.Construction.parameterChangedCover_surjective CharacterPicardBaseChange.Construction.parameterChangedCover_presentation

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable (f' : (Over.pullback s).obj A ⟶ (Over.pullback s).obj B) [IsMonHom f']
variable (hf : f' = (Over.pullback s).map f)

local instance cartierCongruencePullbackMonoidal : (Over.pullback s).Monoidal :=
  Over.instBraidedPullback.toMonoidal

def nativeKernelBaseChangeAlong :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f') ⟶ (Over.pullback s).mapGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) := by
  subst f'
  exact CharacterBaseChangeValues.Construction.nativeKernelBaseChangeInverseGroup s f

theorem nativeKernelBaseChangeAlong_inclusion :
    (nativeKernelBaseChangeAlong s f f' hf).hom.hom ≫ (Over.pullback s).map (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) =
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion f' := by
  subst f'
  change (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv ≫ (Over.pullback s).map (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) = _
  rw [← Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso_inclusion s f, Iso.inv_hom_id_assoc]

variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

def nativeCartierBaseChangeAlong : (C.baseChange s).dual ⟶ C'.dual :=
  (C.baseChange s).dualMap C' (nativeKernelBaseChangeAlong s f f' hf)

theorem nativeCartierBaseChangeAlong_refl
    (C'' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))) :
    nativeCartierBaseChangeAlong s f ((Over.pullback s).map f) rfl C C'' =
      nativeCartierBaseChangeMap s f C C'' := rfl

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

include hf in
omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsMonHom f'] [LocallyOfFinitePresentation f.left] in
theorem nativeChangedCoverAlong_affine : IsAffineHom f'.left :=
  (congrArg (fun z => IsAffineHom z.left) hf).mpr (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).1

include hf in
omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsMonHom f'] [LocallyOfFinitePresentation f.left] in
theorem nativeChangedCoverAlong_flat : Flat f'.left :=
  (congrArg (fun z => Flat z.left) hf).mpr (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.1

include hf in
omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsMonHom f'] [LocallyOfFinitePresentation f.left] in
theorem nativeChangedCoverAlong_surjective : Surjective f'.left :=
  (congrArg (fun z => Surjective z.left) hf).mpr (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.2

include hf in
omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsMonHom f']
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] in
theorem nativeChangedCoverAlong_presentation : LocallyOfFinitePresentation f'.left :=
  (congrArg (fun z => LocallyOfFinitePresentation z.left) hf).mpr
    (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.baseChangedCover_locallyOfFinitePresentation f (Over.mk s))

def nativeCartierPicardChangedMap : C'.dual.X ⟶ (Over.pullback s).obj D.abelian := by
  letI := nativeChangedCoverAlong_affine s f f' hf
  letI := nativeChangedCoverAlong_flat s f f' hf
  letI := nativeChangedCoverAlong_surjective s f f' hf
  letI := nativeChangedCoverAlong_presentation s f f' hf
  exact CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' (D.pullback s) C'

theorem nativeCartierPicard_baseChange_along :
    (nativeCartierBaseChangeAlong s f f' hf C C').hom.hom ≫
        nativeCartierPicardChangedMap s f f' hf C' D =
      (Over.pullback s).map (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  cases hf
  rw [nativeCartierBaseChangeAlong_refl]
  unfold nativeCartierPicardChangedMap
  have hknown := nativeCartierPicard_baseChange s f C C' D
  refine Eq.trans ?_ hknown
  apply congrArg (fun z : C'.dual.X ⟶ (Over.pullback s).obj D.abelian =>
    (nativeCartierBaseChangeMap s f C C').hom.hom ≫ z)
  rfl

end

/-! The source and Cartier comparison maps retain the original kernel
points and character evaluations on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable (f' : (Over.pullback s).obj A ⟶ (Over.pullback s).obj B) [IsMonHom f']
variable (hf : f' = (Over.pullback s).map f)

def nativeKernelBaseChangeAlongPoint (Q : Over S') (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    (Over.map s).obj Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
  (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) Q).symm
    (x ≫ (nativeKernelBaseChangeAlong s f f' hf).hom.hom)

theorem nativeKernelBaseChangeAlongPoint_inclusion (Q : Over S') (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    nativeKernelBaseChangeAlongPoint s f f' hf Q x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f =
      Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s Q (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f') := by
  have hi := congrArg (fun t => x ≫ t) (nativeKernelBaseChangeAlong_inclusion s f f' hf)
  have hn := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm
    (x ≫ (nativeKernelBaseChangeAlong s f f' hf).hom.hom) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
  exact hn.symm.trans (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s Q)
    ((Category.assoc _ _ _).trans hi))

variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
variable (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')))

theorem nativeCartierBaseChangeAlong_evaluation (Q : Over S')
    (d : Q ⟶ (C.baseChange s).dual.X) (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    C'.evaluationValue Q (d ≫ (nativeCartierBaseChangeAlong s f f' hf C C').hom.hom) x =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
        (C.evaluationValue ((Over.map s).obj Q) (C.baseChangeOriginalPoint s Q d)
          (nativeKernelBaseChangeAlongPoint s f f' hf Q x)) :=
  ((C.baseChange s).dualMap_evaluation C' (nativeKernelBaseChangeAlong s f f' hf) Q d x).trans
    (C.baseChange_evaluation s Q d (x ≫ (nativeKernelBaseChangeAlong s f f' hf).hom.hom))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction
