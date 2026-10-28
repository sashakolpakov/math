import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Parameter Group Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints

noncomputable section

/-!
# CartierDuality: actual group and kernel coordinates under parameter restriction
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- Parameter restriction of actual group-scheme points, retaining the group law. -/
def parameterGroupPoint (A : Over S) [GrpObj A] {P Q : Over S} (t : P ⟶ Q) (U : Over P.left) :
    (U ⟶ (Over.pullback P.hom).obj A) →* ((Over.map t.left).obj U ⟶ (Over.pullback Q.hom).obj A) :=
  (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) ((Over.map t.left).obj U)).toMonoidHom.comp
    (((yonedaGrp.obj (Grp.mk A)).map (ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso t U).hom.op).hom.comp
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom (Grp.mk A) U).symm.toMonoidHom)

theorem parameterGroupPoint_original (A : Over S) [GrpObj A] {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ (Over.pullback P.hom).obj A) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) ((Over.map t.left).obj U)).symm
      (parameterGroupPoint A t U x) =
        (ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso t U).hom ≫ (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom (Grp.mk A) U).symm x :=
  (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) ((Over.map t.left).obj U)).symm_apply_apply _

/-- The point restriction uses exactly the native map of fiber products. -/
theorem parameterGroupPoint_left (A : Over S) [GrpObj A] {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ (Over.pullback P.hom).obj A) :
    (parameterGroupPoint A t U x).left = x.left ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t := by
  apply pullback.hom_ext
  · have h := congrArg Over.Hom.left (parameterGroupPoint_original A t U x)
    rw [ParameterKernelPoints.Construction.KernelCharacters.pullbackPoint_original_left, Over.comp_left, ParameterKernelPoints.Construction.KernelCharacters.pullbackPoint_original_left] at h
    change (parameterGroupPoint A t U x).left ≫ pullback.fst A.hom Q.hom =
      (𝟙 U.left) ≫ x.left ≫ pullback.fst A.hom P.hom at h
    rw [Category.id_comp] at h
    exact h.trans (by rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst])
  · rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd, ← Category.assoc]
    exact (Over.w (parameterGroupPoint A t U x)).trans (congrArg (fun a => a ≫ t.left) x.w).symm

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B)

/-- Restriction of points commutes with the actual morphism of groups. -/
theorem parameterGroupPoint_comp {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ (Over.pullback P.hom).obj A) :
    parameterGroupPoint B t U (x ≫ (Over.pullback P.hom).map f) =
      parameterGroupPoint A t U x ≫ (Over.pullback Q.hom).map f := by
  apply Over.OverMorphism.ext
  rw [parameterGroupPoint_left, Over.comp_left, Over.comp_left, parameterGroupPoint_left]
  simp only [Category.assoc]
  rw [ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square]

variable [IsMonHom f]

/-- The image of a restricted kernel point is the restricted image of the original kernel point. -/
theorem parameterKernelPoint_inclusion {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback P.hom).map f)) :
    ParameterKernelPoints.Construction.KernelCharacters.parameterKernelPoint f t U x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map f) =
      parameterGroupPoint A t U (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback P.hom).map f)) := by
  apply (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) ((Over.map t.left).obj U)).symm.injective
  rw [← KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion, ParameterKernelPoints.Construction.KernelCharacters.parameterKernelPoint_original,
    parameterGroupPoint_original, Category.assoc, KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion]

omit [IsMonHom f] in
/-- Equal-image pairs retain equal images after parameter restriction. -/
theorem parameterGroupPoint_equalImage {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x y : U ⟶ (Over.pullback P.hom).obj A)
    (h : x ≫ (Over.pullback P.hom).map f = y ≫ (Over.pullback P.hom).map f) :
    parameterGroupPoint A t U x ≫ (Over.pullback Q.hom).map f =
      parameterGroupPoint A t U y ≫ (Over.pullback Q.hom).map f :=
  (parameterGroupPoint_comp f t U x).symm.trans
    ((congrArg (parameterGroupPoint B t U) h).trans (parameterGroupPoint_comp f t U y))

/-- Restriction preserves the actual kernel difference of any two covering points. -/
theorem parameterKernelPoint_difference {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x y : U ⟶ (Over.pullback P.hom).obj A)
    (h : x ≫ (Over.pullback P.hom).map f = y ≫ (Over.pullback P.hom).map f) :
    ParameterKernelPoints.Construction.KernelCharacters.parameterKernelPoint f t U (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference ((Over.pullback P.hom).map f) x y h) =
      KernelCharacterGluing.Construction.KernelCharacters.kernelDifference ((Over.pullback Q.hom).map f) (parameterGroupPoint A t U x) (parameterGroupPoint A t U y)
        (parameterGroupPoint_equalImage f t U x y h) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map f)) :=
    inferInstanceAs (Mono (equalizer.ι ((Over.pullback Q.hom).map f) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map f))).mp
  rw [parameterKernelPoint_inclusion, KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, map_mul, map_inv]

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints
