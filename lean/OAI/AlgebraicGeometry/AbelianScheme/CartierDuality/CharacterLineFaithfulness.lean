import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality

/-! # Character Line Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness

noncomputable section

/-!
# CartierDuality: actual character lines distinguish characters
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters
section

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The actual unit-valued kernel character over its parameter determines the original internal-Hom section. -/
theorem parameterKernelCharacter_injective (Q : Over S) : Function.Injective (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q) := by
  intro χ ψ h
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  let U : Over Q.left := Over.mk V.unop.hom.left
  let e : (Over.map Q.hom).obj U ≅ V.unop.left :=
    Over.isoMk (Iso.refl V.unop.left.left) (by
      change (𝟙 V.unop.left.left) ≫ V.unop.left.hom = V.unop.hom.left ≫ Q.hom
      rw [Category.id_comp, V.unop.hom.w])
  let a : Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U) ⟶ V.unop := Over.homMk e.hom (by
    apply Over.OverMorphism.ext
    exact Category.id_comp _)
  let z' := (ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom U).symm (e.hom ≫ z)
  have hz : KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z' = e.hom ≫ z :=
    (ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom U).apply_symm_apply _
  have hu := congrArg (fun p => p U z') h
  have hu' : χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z') =
      ψ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z') :=
    UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective ((Over.map Q.hom).obj U) hu
  have hx := χ.naturality_apply a.op z
  have hy := ψ.naturality_apply a.op z
  apply (cancel_epi e.hom).mp
  exact hx.symm.trans ((congrArg (χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))) hz.symm).trans
    (hu'.trans ((congrArg (ψ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))) hz).trans hy)))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

/-- With no extra source functions, isomorphic descended lines recover the same actual kernel character. -/
theorem character_eq_of_lineClass_eq (hp : Function.Surjective A.hom.appTop)
    (χ ψ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))
    (hψ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x))
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ)) :
    χ = ψ := by
  obtain ⟨e⟩ := Quotient.exact h
  funext T
  apply MonoidHom.ext
  intro z
  apply Units.ext
  let x : T ⟶ A := 1
  let y : T ⟶ A := x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
  have hy : y ≫ f = x ≫ f := Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z
  have hc := LineCharacterIndependence.Construction.KernelCharacters.canonicalScalar_eq_of_lineIso A.hom hp f.left
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ) e
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f ψ hψ)
    (x ≫ f).left x.left y.left rfl (congrArg Over.Hom.left hy) (x.w.trans y.w.symm)
  exact (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_kernelValue f χ hχ x z).symm.trans
    (hc.trans (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_kernelValue f ψ hψ x z))

/-- Injectivity of the actual line-class construction over any parameter with the source-functions property. -/
theorem parameterCharacterLine_class_injective (Q : Over S)
    (hp : Function.Surjective ((Over.pullback Q.hom).obj A).hom.appTop) :
    Function.Injective (fun χ => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  intro χ ψ h
  apply parameterKernelCharacter_injective f Q
  exact character_eq_of_lineClass_eq ((Over.pullback Q.hom).map f) hp
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q ψ) h

/-- The original family-line classes distinguish the same actual Cartier sections. -/
theorem parameterLineClass_injective (Q : Over S)
    (hp : Function.Surjective ((Over.pullback Q.hom).obj A).hom.appTop) :
    Function.Injective (fun χ => ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) := by
  intro χ ψ h
  apply parameterCharacterLine_class_injective f Q hp
  apply (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso (pullbackSymmetry Q.hom B.hom)).injective
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q ψ)) at h
  rw [ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry] at h
  exact h

end

variable {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- A proper smooth connected group retains the source-functions property after any affine parameter change. -/
theorem properGroup_parameter_appTop_isIso (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    IsIso ((Over.pullback Q.hom).obj A).hom.appTop := by
  let e := pullbackSymmetry Q.hom A.hom
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))
  have h : IsIso (e.hom ≫ pullback.snd A.hom Q.hom).appTop := by
    rw [pullbackSymmetry_hom_comp_snd]
    exact Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso A Q
  rw [Scheme.Hom.comp_appTop] at h
  exact (isIso_comp_right_iff _ e.hom.appTop).mp h

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness
