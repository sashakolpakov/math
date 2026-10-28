import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Character Point Base Change -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.PoincareBundle.CharacterPointBaseChange

/-! Character-line base change proves equality of the actual Weil character values, including on nonreduced parameter schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

variable {k : Type} [Field k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

/-- Equality of actual Poincare points detects equality of all Cartier sections. -/
theorem point_injective (T : Over (Spec (.of k))) :
    Function.Injective (fun χ => AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D) := by
  intro χ ψ h
  apply AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective f T
  exact (D.representable.homEquiv.apply_symm_apply _).symm.trans
    ((congrArg D.representable.homEquiv h).trans (D.representable.homEquiv.apply_symm_apply _))

variable {K : Type} [Field K] (s : Spec (.of K) ⟶ Spec (.of k))

local instance changedAffine : IsAffineHom ((Over.pullback s).map f).left :=
  (AbelianScheme.CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).1
local instance changedFlat : Flat ((Over.pullback s).map f).left :=
  (AbelianScheme.CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.1
local instance changedSurjective : Surjective ((Over.pullback s).map f).left :=
  (AbelianScheme.CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.2
local instance changedPresentation : LocallyOfFinitePresentation ((Over.pullback s).map f).left :=
  AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange.Construction.parameterChangedCover_presentation s f
local instance changedSmooth : Smooth ((Over.pullback s).obj A).hom :=
  inferInstanceAs (Smooth (pullback.snd A.hom s))
local instance changedProper : IsProper ((Over.pullback s).obj A).hom :=
  inferInstanceAs (IsProper (pullback.snd A.hom s))
local instance changedConnected : GeometricallyConnected ((Over.pullback s).obj A).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))

/-- Two recovered Poincare points identify the base-changed character; compatibility is proved by character-line descent. -/
theorem character_eq (T : Over (Spec (.of K)))
    (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj T)))
    (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of K)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.obj (.op T))
    (p : T ⟶ (D.pullback s).abelian)
    (hχ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f ((Over.map s).obj T) χ D = Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s T p)
    (hψ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((Over.pullback s).map f) T ψ (D.pullback s) = p) :
    ψ = AbelianScheme.FrobeniusKernel.CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f T χ := by
  apply point_injective ((Over.pullback s).map f) (D.pullback s) T
  apply (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s T).injective
  exact (congrArg (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s T) hψ).trans
    (hχ.symm.trans (AbelianScheme.FrobeniusKernel.CharacterPicardBaseChange.Construction.parameterCharacterDualPoint_baseChange s T f χ D).symm)

/-- The regular Weil-character unit is unchanged by the canonical kernel base-change comparison. -/
theorem value_eq (T : Over (Spec (.of K)))
    (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj T)))
    (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of K)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.obj (.op T))
    (p : T ⟶ (D.pullback s).abelian)
    (hχ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f ((Over.map s).obj T) χ D = Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s T p)
    (hψ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((Over.pullback s).map f) T ψ (D.pullback s) = p)
    (z : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ z) =
      AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj T) (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f T z)) := by
  exact (congrArg (fun (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of K)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.obj (.op T)) =>
    AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ z))
    (character_eq f D s T χ ψ p hχ hψ)).trans
      (AbelianScheme.FrobeniusKernel.CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection_unitValue s f T χ z)

end AlgebraicGeometry.Picard.PoincareBundle.CharacterPointBaseChange

namespace AlgebraicGeometry.Picard.PoincareBundle.CharacterPointBaseChange.Congr

/-! The actual character comparison respects a proved equality between a pulled scalar map and the scalar of the pulled group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters

variable {k K : Type} [Field k] [Field K] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (s : Spec (.of K) ⟶ Spec (.of k))
  (g : (Over.pullback s).obj A ⟶ (Over.pullback s).obj B) [IsMonHom g]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left] [LocallyOfFinitePresentation g.left]
  (hg : (Over.pullback s).map f = g)

/-- No compatibility is postulated: the proved equality of scalar maps transports the character-line base-change theorem. -/
theorem value_eq (T : Over (Spec (.of K)))
    (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj T)))
    (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of K)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme g))).obj.obj (.op T))
    (p : T ⟶ (D.pullback s).abelian)
    (hχ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f ((Over.map s).obj T) χ D = Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s T p)
    (hψ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint g T ψ (D.pullback s) = p)
    (z : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme g) :
    AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ z) =
      AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj T) (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ
        (AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f T (z ≫ eqToHom (congrArg
          (fun q : (Over.pullback s).obj A ⟶ (Over.pullback s).obj B => Homomorphisms.Kernel.Construction.kernelScheme q) hg.symm)))) := by
  cases hg
  simpa only [eqToHom_refl, Category.comp_id] using
    CharacterPointBaseChange.value_eq f D s T χ ψ p hχ hψ z

end AlgebraicGeometry.Picard.PoincareBundle.CharacterPointBaseChange.Congr

end

end OAI
