import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RestrictedSheafInjection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

/-! # Geometric Character Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricCharacterMonomorphism

noncomputable section

/-! The actual relative character-line morphism is monic on every geometric fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S)

/-- Every affine parameter on a field fiber has the required source-functions property. -/
theorem geometricParameter_appTop_isIso (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    IsIso ((Over.pullback ((Over.map s).obj Q).hom).obj A).hom.appTop := by
  let A' := (Over.pullback s).obj A
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom s))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))
  let e : (Over.pullback ((Over.map s).obj Q).hom).obj A ≅ (Over.pullback Q.hom).obj A' :=
    (Over.pullbackComp Q.hom s).app A
  have h : IsIso ((Over.pullback Q.hom).obj A').hom.appTop := CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A' Q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Q.left).map e.hom))
  have : IsIso e.hom.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.left.op))
  rw [← e.hom.w, Scheme.Hom.comp_appTop]
  infer_instance

variable {A} {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- Character-line classes remain injective on all affine parameters of a field fiber. -/
theorem geometricParameterHomogeneousClass_injective_affine
    (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    Function.Injective (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f ((Over.map s).obj Q)) := by
  have : IsIso ((Over.pullback ((Over.map s).obj Q).hom).obj A).hom.appTop :=
    geometricParameter_appTop_isIso A s Q
  intro χ ψ h
  apply CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f ((Over.map s).obj Q)
    (ConcreteCategory.bijective_of_isIso ((Over.pullback ((Over.map s).obj Q).hom).obj A).hom.appTop).surjective
  exact (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f ((Over.map s).obj Q) χ).symm.trans
    ((congrArg Subtype.val h).trans (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f ((Over.map s).obj Q) ψ))

/-- Affine cover density retains every infinitesimal test on the field fiber. -/
theorem geometricParameterHomogeneousClass_injective (Q : Over (Spec (.of k))) :
    Function.Injective (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f ((Over.map s).obj Q)) := by
  let X := (Scheme.fppfTopology.overMapPullback (Type (u + 1)) s).obj
    (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  have hd : (algSpec (.of k)).IsCoverDense (Scheme.fppfTopology.over (Spec (.of k))) :=
    SheafDescent.Construction.e56AlgSpecCoverDense (.of k)
  intro χ ψ h
  apply Functor.IsCoverDense.ext (algSpec (.of k)) X Q
  intro R t
  have : IsAffine ((algSpec (.of k)).obj R).left := by change IsAffine (Spec _); infer_instance
  apply geometricParameterHomogeneousClass_injective_affine s f ((algSpec (.of k)).obj R)
  exact (ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f ((Over.map s).map t) χ).symm.trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map ((Over.map s).map t).op) h).trans
      (ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f ((Over.map s).map t) ψ))

/-- The actual Picard sheaf map is injective on every parameter of a field fiber. -/
theorem geometricParameterPicardHom_injective (Q : Over (Spec (.of k))) :
    Function.Injective (ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f ((Over.map s).obj Q)) :=
  RestrictedSheafInjection.Construction.Schemes.restricted_sheafification_injective s
    (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)
    (PicardMonomorphism.Construction.KernelCharacters.parameterCharacterRawMap f) (geometricParameterHomogeneousClass_injective s f) Q

variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

/-- The original relative character-line map is a monomorphism after any field base change. -/
theorem cartierToPicard_geometric_mono : Mono ((Over.pullback s).map (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C)) := by
  constructor
  intro Q x y h
  apply (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s C.dual Q).symm.injective
  apply (C.sectionEquiv ((Over.map s).obj Q)).injective
  apply geometricParameterPicardHom_injective s f Q
  have hx := PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C ((Over.map s).obj Q)
    ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s C.dual Q).symm x)
  have hy := PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C ((Over.map s).obj Q)
    ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s C.dual Q).symm y)
  have hc := congrArg ((Over.mapPullbackAdj s).homEquiv Q D.abelian).symm h
  rw [(Over.mapPullbackAdj s).homEquiv_naturality_right_symm,
    (Over.mapPullbackAdj s).homEquiv_naturality_right_symm] at hc
  have hr := congrArg D.representable.homEquiv (hx.symm.trans (hc.trans hy))
  exact (D.representable.homEquiv.apply_symm_apply _).symm.trans
    (hr.trans (D.representable.homEquiv.apply_symm_apply _))

variable (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

/-- Factoring through dual torsion preserves the geometric monomorphism. -/
theorem cartierToPicardTorsion_geometric_mono :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Mono ((Over.pullback s).map (CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C)) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : Mono ((Over.pullback s).map (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C)) := cartierToPicard_geometric_mono s f D C
  constructor
  intro Q x y h
  apply (cancel_mono ((Over.pullback s).map (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C))).mp
  rw [← CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f D n hn C, Functor.map_comp,
    ← Category.assoc, ← Category.assoc, h]

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricCharacterMonomorphism
