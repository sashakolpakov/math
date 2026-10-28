import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf

/-! # Character Unit Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

noncomputable section

/-!
# CartierDuality: internal-Hom characters give regular units on every test scheme
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- The Laurent generator as a group-like coordinate of the integral multiplicative group. -/
def multiplicativeGroupGenerator : GroupLike (ULift.{u} ℤ) (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) :=
  ⟨MonoidAlgebra.of (ULift.{u} ℤ) (Multiplicative ℤ) (Multiplicative.ofAdd 1),
    MonoidAlgebra.isGroupLikeElem_of (R := ULift.{u} ℤ) (A := ULift.{u} ℤ) (Multiplicative.ofAdd 1)⟩

/-- The regular unit represented by an actual point of the multiplicative group. -/
def multiplicativeGroupUnitHom {S : Scheme.{u}} (T : Over S) :
    (T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) →* Γ(T.left, ⊤)ˣ :=
  (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ) (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
    multiplicativeGroupGenerator ((Over.map (specULiftZIsTerminal.from S)).obj T)).comp
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv (specULiftZIsTerminal.from S) (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)) T).symm.toMonoidHom

/-- The unit value restricts by the actual map of structure sheaves. -/
theorem multiplicativeGroupUnitHom_natural {S : Scheme.{u}} {T U : Over S}
    (t : U ⟶ T) (x : T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :
    Units.map t.left.appTop.hom (multiplicativeGroupUnitHom T x) =
      multiplicativeGroupUnitHom U (t ≫ x) := by
  let p := specULiftZIsTerminal.from S
  let G := Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
  have hn := HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom_natural (ULift.{u} ℤ)
    (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) multiplicativeGroupGenerator
      ((Over.map p).map t) ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T).symm x)
  exact hn.trans (congrArg
    (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ) (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
      multiplicativeGroupGenerator ((Over.map p).obj U))
    (KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_precomp p G t x).symm)

end Construction.Schemes

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- The structural map to the parameter scheme as a morphism over the original base. -/
def parameterProjection (Q : Over S) (U : Over Q.left) : (Over.map Q.hom).obj U ⟶ Q :=
  Over.homMk U.hom

theorem parameterProjection_natural (Q : Over S) {U V : Over Q.left} (t : V ⟶ U) :
    (Over.map Q.hom).map t ≫ parameterProjection Q U = parameterProjection Q V := by
  apply Over.OverMorphism.ext
  exact t.w

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (Q : Over S) (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- An internal-Hom section becomes the actual unit-valued character of the kernel over its parameter. -/
def parameterKernelCharacter (U : Over Q.left) :
    (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(U.left, ⊤)ˣ :=
  (Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)).comp
    ((χ.app (.op (Over.mk (parameterProjection Q U)))).hom.comp (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U))

/-- All test-scheme restrictions of the character agree, including infinitesimal tests. -/
theorem parameterKernelCharacter_natural {U V : Over Q.left} (t : V ⟶ U)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    Units.map t.left.appTop.hom (parameterKernelCharacter f Q χ U x) =
      parameterKernelCharacter f Q χ V (t ≫ x) := by
  let a : Over.mk (parameterProjection Q V) ⟶ Over.mk (parameterProjection Q U) :=
    Over.homMk ((Over.map Q.hom).map t) (parameterProjection_natural Q t)
  have hn := χ.naturality_apply a.op (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U x)
  have hv := Schemes.multiplicativeGroupUnitHom_natural ((Over.map Q.hom).map t)
    (χ.app (.op (Over.mk (parameterProjection Q U))) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U x))
  exact hv.trans (congrArg (Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj V))
    (hn.symm.trans (congrArg (χ.app (.op (Over.mk (parameterProjection Q V))))
      (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_natural Q.hom f t x).symm)))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues
