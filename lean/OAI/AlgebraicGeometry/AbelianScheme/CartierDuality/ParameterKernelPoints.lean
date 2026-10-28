import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

/-! # Parameter Kernel Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

noncomputable section

/-!
# CartierDuality: scheme-theoretic kernel points under parameter restriction
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- The two original-base descriptions of a test scheme under parameter restriction. -/
def parameterTestIso {P Q : Over S} (t : P ⟶ Q) (U : Over P.left) :
    (Over.map Q.hom).obj ((Over.map t.left).obj U) ≅ (Over.map P.hom).obj U :=
  Over.isoMk (Iso.refl U.left) (by
    change (𝟙 U.left) ≫ (U.hom ≫ P.hom) = (U.hom ≫ t.left) ≫ Q.hom
    rw [Category.id_comp, Category.assoc, t.w])

/-- The comparison retains the structural morphism to the parameter scheme. -/
theorem parameterTestIso_projection {P Q : Over S} (t : P ⟶ Q) (U : Over P.left) :
    (parameterTestIso t U).hom ≫ CharacterUnitValues.Construction.KernelCharacters.parameterProjection P U ≫ t =
      CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q ((Over.map t.left).obj U) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The native kernel base-change comparison is an equivalence of point groups. -/
def baseChangeKernelPointMulEquiv {S' : Scheme.{u}} (s : S' ⟶ S) (U : Over S') :
    (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) ≃* ((Over.map s).obj U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) := by
  have := KernelCharacterBaseChange.Construction.KernelCharacters.kernelBaseChangeIso_inv_isMonHom s f
  let e : (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) ≃*
      (U ⟶ (Over.pullback s).obj (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) :=
    { toEquiv := (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).symm.homToEquiv
      map_mul' x y := MonObj.mul_comp x y (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv }
  exact e.trans (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) U).symm

theorem baseChangeKernelPointMulEquiv_apply {S' : Scheme.{u}} (s : S' ⟶ S) (U : Over S')
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    baseChangeKernelPointMulEquiv f s U x = KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f U x := rfl

/-- Restriction of kernel points, via the canonical pullback equivalences and original-base test comparison. -/
def parameterKernelPoint {P Q : Over S} (t : P ⟶ Q) (U : Over P.left) :
    (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback P.hom).map f)) →*
      ((Over.map t.left).obj U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :=
  (baseChangeKernelPointMulEquiv f Q.hom ((Over.map t.left).obj U)).symm.toMonoidHom.comp
    (((yonedaGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).map (parameterTestIso t U).hom.op).hom.comp
      (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint P.hom f U))

/-- Restriction retains exactly the original kernel point through the canonical test comparison. -/
theorem parameterKernelPoint_original {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback P.hom).map f)) :
    KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f ((Over.map t.left).obj U) (parameterKernelPoint f t U x) =
      (parameterTestIso t U).hom ≫ KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint P.hom f U x :=
  (baseChangeKernelPointMulEquiv f Q.hom ((Over.map t.left).obj U)).apply_symm_apply _

/-- The original point of a base-changed group is given by its actual scheme projection. -/
theorem pullbackPoint_original_left {S' : Scheme.{u}} (s : S' ⟶ S) (G : Grp (Over S)) (U : Over S')
    (x : U ⟶ (Over.pullback s).obj G.X) :
    ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G U).symm x).left = x.left ≫ pullback.fst G.X.hom s := rfl

/-- Restricting a kernel point preserves its actual original group coordinate. -/
theorem parameterKernelPoint_groupCoordinate {P Q : Over S} (t : P ⟶ Q) (U : Over P.left)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback P.hom).map f)) :
    (parameterKernelPoint f t U x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback Q.hom).map f)).left ≫
      pullback.fst A.hom Q.hom =
    (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback P.hom).map f)).left ≫ pullback.fst A.hom P.hom := by
  have h := congrArg (fun z => (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left) (parameterKernelPoint_original f t U x)
  have hq := congrArg Over.Hom.left (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion Q.hom f
    ((Over.map t.left).obj U) (parameterKernelPoint f t U x))
  have hp := congrArg Over.Hom.left (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion P.hom f U x)
  rw [pullbackPoint_original_left] at hq hp
  have he : ((parameterTestIso t U).hom ≫ KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint P.hom f U x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left =
      (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint P.hom f U x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left := by
    change (𝟙 U.left) ≫ _ = _
    exact Category.id_comp _
  exact hq.symm.trans (h.trans (he.trans hp))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints
