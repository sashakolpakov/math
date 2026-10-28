import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Parameter Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterSection

noncomputable section

/-! Reassemble a natural unit character of the pulled-back kernel as an
actual internal-Hom character section on the original parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

variable {S : Scheme.{u}} (Q : Over S)

def kernelParameterTest (V : Over Q) : Over Q.left := Over.mk V.hom.left

def kernelParameterOriginalIso (V : Over Q) :
    (Over.map Q.hom).obj (kernelParameterTest Q V) ≅ V.left :=
  Over.isoMk (Iso.refl V.left.left) (by
    change (𝟙 V.left.left) ≫ V.left.hom = V.hom.left ≫ Q.hom
    exact (Category.id_comp _).trans V.hom.w.symm)

def kernelParameterTestMap {V W : Over Q} (t : W ⟶ V) :
    kernelParameterTest Q W ⟶ kernelParameterTest Q V :=
  Over.homMk t.left.left (congrArg Over.Hom.left t.w)

theorem kernelParameterOriginalIso_natural {V W : Over Q} (t : W ⟶ V) :
    (Over.map Q.hom).map (kernelParameterTestMap Q t) ≫ (kernelParameterOriginalIso Q V).hom =
      (kernelParameterOriginalIso Q W).hom ≫ t.left := by
  apply Over.OverMorphism.ext
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def kernelParameterPoint (V : Over Q) :
    (V.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →*
      (kernelParameterTest Q V ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :=
  (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (kernelParameterTest Q V)).symm.toMonoidHom.comp
    ((yonedaGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).map (kernelParameterOriginalIso Q V).hom.op).hom

theorem kernelParameterPoint_original (V : Over Q) (z : V.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f (kernelParameterTest Q V) (kernelParameterPoint Q f V z) =
      (kernelParameterOriginalIso Q V).hom ≫ z :=
  (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (kernelParameterTest Q V)).apply_symm_apply _

theorem kernelParameterPoint_natural {V W : Over Q} (t : W ⟶ V) (z : V.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    kernelParameterPoint Q f W (t.left ≫ z) =
      kernelParameterTestMap Q t ≫ kernelParameterPoint Q f V z := by
  apply (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (kernelParameterTest Q W)).injective
  change CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _ = CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _
  rw [kernelParameterPoint_original, CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_natural, kernelParameterPoint_original]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ z) (kernelParameterOriginalIso_natural Q t).symm).trans
      (Category.assoc _ _ _))

theorem kernelParameterPoint_projection (T : Over Q.left)
    (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    kernelParameterPoint Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q T))
      (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f T z) = z := by
  apply (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom T).injective
  have hp := kernelParameterPoint_original Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q T))
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f T z)
  have he : (kernelParameterOriginalIso Q (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q T))).hom =
      𝟙 ((Over.map Q.hom).obj T) := by
    apply Over.OverMorphism.ext
    rfl
  exact hp.trans ((congrArg (fun a => a ≫ CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f T z) he).trans
    (Category.id_comp _))

variable (χ : ∀ T : Over Q.left,
  (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(T.left, ⊤)ˣ)
variable (hχ : ∀ {T U : Over Q.left} (t : U ⟶ T)
  (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
  Units.map t.left.appTop.hom (χ T z) = χ U (t ≫ z))

def parameterSectionOfUnitCharacter :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q) where
  app V := GrpCat.ofHom ((MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv V.unop.left).symm.toMonoidHom.comp
    ((χ (kernelParameterTest Q V.unop)).comp (kernelParameterPoint Q f V.unop)))
  naturality {V W} t := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    change V.unop.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f at z
    change (MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv W.unop.left).symm
      (χ (kernelParameterTest Q W.unop) (kernelParameterPoint Q f W.unop (t.unop.left ≫ z))) =
      t.unop.left ≫ (MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv V.unop.left).symm
        (χ (kernelParameterTest Q V.unop) (kernelParameterPoint Q f V.unop z))
    rw [kernelParameterPoint_natural Q f t.unop z]
    exact (congrArg (MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv W.unop.left).symm
      (hχ (kernelParameterTestMap Q t.unop) (kernelParameterPoint Q f V.unop z)).symm).trans
      (MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv_natural t.unop.left _).symm

theorem parameterSectionOfUnitCharacter_value (T : Over Q.left)
    (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (parameterSectionOfUnitCharacter Q f χ hχ) T z = χ T z := by
  change CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj T)
    ((MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv ((Over.map Q.hom).obj T)).symm
      (χ (kernelParameterTest Q (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q T)))
        (kernelParameterPoint Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q T))
          (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f T z)))) = χ T z
  rw [kernelParameterPoint_projection]
  exact (MultiplicativeUnitPoints.Construction.multiplicativeGroupUnitEquiv ((Over.map Q.hom).obj T)).apply_symm_apply _

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterSection
