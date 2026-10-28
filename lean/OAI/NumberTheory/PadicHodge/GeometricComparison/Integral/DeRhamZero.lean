import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionCycle
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalDifferential

/-! # De Rham Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamZero.IntegralDeRhamHZero

noncomputable section

/-! Actual integral de Rham H-zero equals the base ring when the global-function map is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (.of R)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X
local notation "N" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X

instance connective : (K).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE ((N).extend ComplexShape.embeddingUpNat) 0
  infer_instance

def termIso (n : ℕ) : (K).X (n : ℤ) ≅ (N).X n :=
  (N).extendXIso ComplexShape.embeddingUpNat rfl

theorem differential_zero [IsIso X.hom.appTop]
    (ω : ((K).X 0).obj.obj (op ⊤)) : ((K).d 0 1).hom.app (op ⊤) ω = 0 := by
  have hd : (K).d 0 1 = (termIso R X 0).hom ≫ (N).d 0 1 ≫ (termIso R X 1).inv :=
    (N).extend_d_eq ComplexShape.embeddingUpNat (i := 0) (j := 1) rfl rfl
  rw [hd]
  change (termIso R X 1).inv.hom.app (op ⊤)
    (((N).d 0 1).hom.app (op ⊤) ((termIso R X 0).hom.hom.app (op ⊤) ω)) = 0
  rw [GlobalDifferential.IntegralGlobalDifferential.sheaf_differential_zero, map_zero]

def kernelEquiv [IsIso X.hom.appTop] : ConnectiveSectionCycle.ConnectiveSectionKernel.sectionKernel R X.left K ≃ₗ[R]
    ((K).X 0).obj.obj (op ⊤) :=
  LinearEquiv.ofBijective (ConnectiveSectionCycle.ConnectiveSectionKernel.sectionKernel R X.left K).subtype
    ⟨Subtype.val_injective, fun ω => ⟨⟨ω, differential_zero R X ω⟩, rfl⟩⟩

def functionsEquiv : ((K).X 0).obj.obj (op ⊤) ≃ₗ[R]
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X).obj (op ⊤) :=
  (((sheafSections (Opens.grothendieckTopology X.left) (ModuleCat R)).obj (op ⊤)).mapIso
    (termIso R X 0 ≪≫ FunctionsSheaf.IntegralFunctionsSheaf.zeroTermIso R X)).toLinearEquiv

def baseEquiv [IsIso X.hom.appTop] : R ≃ₗ[R]
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X).obj (op ⊤) := by
  let B := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op ⊤)
  apply LinearEquiv.ofBijective (Algebra.linearMap R B)
  have hX := (ConcreteCategory.isIso_iff_bijective X.hom.appTop).mp inferInstance
  change Function.Bijective (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤)
  convert hX.comp (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective using 1
  funext r
  simp [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

def unshift : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 0 ≃ₗ[R]
    ((DerivedCategory.singleFunctor V 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) ⟶
      DerivedCategory.Q.obj K) :=
  Linear.homCongr R (Iso.refl _)
    ((shiftFunctorZero (DerivedCategory V) ℤ).app (DerivedCategory.Q.obj K))

def equiv [IsIso X.hom.appTop] : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 0 ≃ₗ[R] R :=
  (unshift R X).trans ((ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X.left K).trans
    ((kernelEquiv R X).trans ((functionsEquiv R X).trans (baseEquiv R X).symm)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamZero.IntegralDeRhamHZero
