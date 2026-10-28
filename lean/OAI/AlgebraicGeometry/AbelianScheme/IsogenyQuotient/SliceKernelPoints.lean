import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Slice Kernel Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceKernelPoints

noncomputable section

/-! Kernel points on the iterated slice are the same actual points as
on schemes over the parameter. The equivalence retains every test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

universe u

variable {S : Scheme.{u}} (Q : Over S)

def parameterSliceTest (V : Over Q) : Over Q.left := Over.mk V.hom.left

def parameterSliceTestIso (V : Over Q) : (Over.map Q.hom).obj (parameterSliceTest Q V) ≅ V.left :=
  Over.isoMk (Iso.refl V.left.left) (by
    change (𝟙 V.left.left) ≫ V.left.hom = V.hom.left ≫ Q.hom
    rw [Category.id_comp, V.hom.w])

def parameterSliceTestMap {V W : Over Q} (a : V ⟶ W) : parameterSliceTest Q V ⟶ parameterSliceTest Q W :=
  Over.homMk a.left.left (congrArg Over.Hom.left a.w)

theorem parameterSliceTestIso_natural {V W : Over Q} (a : V ⟶ W) :
    (Over.map Q.hom).map (parameterSliceTestMap Q a) ≫ (parameterSliceTestIso Q W).hom =
      (parameterSliceTestIso Q V).hom ≫ a.left := by
  apply Over.OverMorphism.ext
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def parameterSliceKernelPoint (V : Over Q) :
    (V.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →*
      (parameterSliceTest Q V ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :=
  (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (parameterSliceTest Q V)).symm.toMonoidHom.comp
    ((yonedaGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).map (parameterSliceTestIso Q V).hom.op).hom

theorem parameterSliceKernelPoint_original (V : Over Q) (z : V.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f (parameterSliceTest Q V) (parameterSliceKernelPoint Q f V z) =
      (parameterSliceTestIso Q V).hom ≫ z :=
  (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (parameterSliceTest Q V)).apply_symm_apply _

theorem parameterSliceKernelPoint_natural {V W : Over Q} (a : V ⟶ W) (z : W.left ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    parameterSliceKernelPoint Q f V (a.left ≫ z) =
      parameterSliceTestMap Q a ≫ parameterSliceKernelPoint Q f W z := by
  apply (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom (parameterSliceTest Q V)).injective
  change CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _ = CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _
  rw [parameterSliceKernelPoint_original, CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_natural, parameterSliceKernelPoint_original]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ z) (parameterSliceTestIso_natural Q a).symm).trans (Category.assoc _ _ _))

theorem parameterSliceKernelPoint_parameter (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    parameterSliceKernelPoint Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)) (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z) = z := by
  apply (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom U).injective
  change CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _ = CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f _ _
  exact (parameterSliceKernelPoint_original Q f (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))
    (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U z)).trans (Category.id_comp _)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceKernelPoints
