import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv

/-! # Character Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection

noncomputable section

/-! A natural unit-valued character of the base-changed kernel gives
an actual section of CartierDuality's original internal-Hom character sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (Q : Over S)
  (χ : ∀ U : Over Q.left, (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(U.left, ⊤)ˣ)
  (hχ : ∀ {U V : Over Q.left} (a : V ⟶ U) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
    Units.map a.left.appTop.hom (χ U z) = χ V (a ≫ z))

def parameterCharacterSection : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q) where
  app V := GrpCat.ofHom ((MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv V.unop.left).symm.toMonoidHom.comp
    ((χ (SliceKernelPoints.Construction.parameterSliceTest Q V.unop)).comp (SliceKernelPoints.Construction.parameterSliceKernelPoint Q f V.unop)))
  naturality := by
    intro V W a
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    change V.unop.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f at z
    change (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv W.unop.left).symm
      (χ (SliceKernelPoints.Construction.parameterSliceTest Q W.unop) (SliceKernelPoints.Construction.parameterSliceKernelPoint Q f W.unop (a.unop.left ≫ z))) =
        a.unop.left ≫ (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv V.unop.left).symm
          (χ (SliceKernelPoints.Construction.parameterSliceTest Q V.unop) (SliceKernelPoints.Construction.parameterSliceKernelPoint Q f V.unop z))
    rw [SliceKernelPoints.Construction.parameterSliceKernelPoint_natural, ← hχ]
    exact MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv_symm_natural a.unop.left _

theorem parameterCharacterSection_value (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (parameterCharacterSection f Q χ hχ) U z = χ U z := by
  change CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)
    ((MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv ((Over.map Q.hom).obj U)).symm
      (χ (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))
        (SliceKernelPoints.Construction.parameterSliceKernelPoint Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))
          (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z)))) = χ U z
  rw [SliceKernelPoints.Construction.parameterSliceKernelPoint_parameter]
  exact (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv ((Over.map Q.hom).obj U)).apply_symm_apply _

theorem parameterCharacterSection_recovers :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (parameterCharacterSection f Q χ hχ) = χ := by
  funext U
  exact MonoidHom.ext (parameterCharacterSection_value f Q χ hχ U)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection
