import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints

/-! # Parameter Character Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterCharacterRestriction

noncomputable section

/-!
# CartierDuality: parameter restriction preserves actual character gluing scalars
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    {P Q : Over S} (t : P ⟶ Q)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- Restricting an internal-Hom section preserves its actual regular-unit value on the restricted kernel. -/
theorem parameterKernelCharacter_restrict (U : Over P.left)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback P.hom).map f)) :
    CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ ((Over.map t.left).obj U) (ParameterKernelPoints.Construction.KernelCharacters.parameterKernelPoint f t U x) =
      CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) U x := by
  let V := (Over.map t.left).obj U
  let e := ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso t U
  let a : Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q V) ⟶ Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection P U ≫ t) :=
    Over.homMk e.hom (ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso_projection t U)
  let z := KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint P.hom f U x
  have hn := χ.naturality_apply a.op z
  have hp := ParameterKernelPoints.Construction.KernelCharacters.parameterKernelPoint_original f t U x
  have hc := (congrArg (χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q V)))) hp).trans hn
  have hv := congrArg (CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj V)) hc
  have hu := CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom_natural e.hom
    (χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection P U ≫ t))) z)
  apply Units.ext
  have hu' := congrArg Units.val hu
  change (𝟙 U.left : U.left ⟶ U.left).appTop
      (CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map P.hom).obj U)
        (χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection P U ≫ t))) z)).val = _ at hu'
  rw [Scheme.Hom.id_appTop] at hu'
  exact (congrArg Units.val hv).trans hu'.symm

omit [GrpObj B] [IsMonHom f] χ in
/-- The image of a covering point is the restricted native image in the parameter square. -/
theorem parameterGroupPoint_image_left (U : Over P.left) (q : U.left ⟶ ((Over.pullback P.hom).obj B).left)
    (x : U ⟶ (Over.pullback P.hom).obj A) (hx : x.left ≫ ((Over.pullback P.hom).map f).left = q) :
    (ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint A t U x).left ≫ ((Over.pullback Q.hom).map f).left = q ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t := by
  rw [ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint_left, Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square, ← Category.assoc, hx]

/-- On an arbitrary over-scheme test pair, restriction preserves the exact character difference scalar. -/
theorem parameterDifferenceScalar_restrict_over (U : Over P.left)
    (q : U.left ⟶ ((Over.pullback P.hom).obj B).left) (x y : U ⟶ (Over.pullback P.hom).obj A)
    (hx : x.left ≫ ((Over.pullback P.hom).map f).left = q)
    (hy : y.left ≫ ((Over.pullback P.hom).map f).left = q) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (q ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint A t U x).left (ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint A t U y).left
      (parameterGroupPoint_image_left f t U q x hx) (parameterGroupPoint_image_left f t U q y hy) =
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback P.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
      q x.left y.left hx hy := by
  let ψ := (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ
  let h : x ≫ (Over.pullback P.hom).map f = y ≫ (Over.pullback P.hom).map f :=
    Over.OverMorphism.ext (hx.trans hy.symm)
  have hnew := CharacterTranslations.Construction.KernelCharacters.differenceScalar_over ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (q ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)
    (ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint A t U x) (ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint A t U y)
    (parameterGroupPoint_image_left f t U q x hx) (parameterGroupPoint_image_left f t U q y hy)
  have hold := CharacterTranslations.Construction.KernelCharacters.differenceScalar_over ((Over.pullback P.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ψ)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f P ψ) q x y hx hy
  have hk := ParameterGroupPoints.Construction.KernelCharacters.parameterKernelPoint_difference f t U x y h
  have hc := parameterKernelCharacter_restrict f t χ U (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference ((Over.pullback P.hom).map f) x y h)
  exact hnew.trans ((congrArg Units.val
    ((congrArg (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ ((Over.map t.left).obj U)) hk.symm).trans hc)).trans hold.symm)

/-- The full native gluing scalar is preserved by the parameter square on every scheme test pair. -/
theorem parameterDifferenceScalar_restrict {T : Scheme.{u}}
    (q : T ⟶ ((Over.pullback P.hom).obj B).left) (x y : T ⟶ ((Over.pullback P.hom).obj A).left)
    (hx : x ≫ ((Over.pullback P.hom).map f).left = q)
    (hy : y ≫ ((Over.pullback P.hom).map f).left = q) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (q ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (x ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t) (y ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t)
      (by rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square, ← Category.assoc, hx])
      (by rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square, ← Category.assoc, hy]) =
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback P.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
      q x y hx hy := by
  let U : Over P.left := Over.mk (q ≫ ((Over.pullback P.hom).obj B).hom)
  let px : U ⟶ (Over.pullback P.hom).obj A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint ((Over.pullback P.hom).map f) q x hx
  let py : U ⟶ (Over.pullback P.hom).obj A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint ((Over.pullback P.hom).map f) q y hy
  have hpx : px.left ≫ ((Over.pullback P.hom).map f).left = q := hx
  have hpy : py.left ≫ ((Over.pullback P.hom).map f).left = q := hy
  have h := parameterDifferenceScalar_restrict_over f t χ U q px py hpx hpy
  simp only [ParameterGroupPoints.Construction.KernelCharacters.parameterGroupPoint_left] at h
  exact h

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterCharacterRestriction
