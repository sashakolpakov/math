import OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleReducedKernels
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainZero
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Homology.QuasiIso

/-! # Adic Reduction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicReduction.Construction

noncomputable section

/-! Actual reduction of module cochain complexes, identified with tensoring by the quotient ring. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Reduction modulo the ideal, retaining the original base scalar structure. -/
def adicReductionFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M ⧸ (I • ⊤ : Submodule R M))
  map f := ModuleCat.ofHom ((f.hom.reduceModIdeal I).restrictScalars R)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

instance : (adicReductionFunctor (R := R) I).Additive where
  map_add := by
    intros M N f g
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The actual tensor-to-quotient identification is natural in the module. -/
def adicReductionTensorIso :
    Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.tensor (R ⧸ I) ≅ adicReductionFunctor I :=
  NatIso.ofComponents (fun M => (TensorProduct.quotTensorEquivQuotSMul M I).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change TensorProduct.quotTensorEquivQuotSMul N I
      (Ideal.Quotient.mk I r ⊗ₜ[R] f x) =
      f.hom.reduceModIdeal I
        (TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I r ⊗ₜ[R] x))
    simp)

abbrev adicReductionComplex (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((adicReductionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

abbrev adicReductionMap {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D) :
    adicReductionComplex I C ⟶ adicReductionComplex I D :=
  ((adicReductionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).map φ

/-- Reduction of the actual cochain complex agrees with its quotient-ring tensor complex. -/
def adicReductionComplexIso (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex (R ⧸ I) C ≅ adicReductionComplex I C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (adicReductionTensorIso I).app (C.X n))
    (fun _ _ _ => ((adicReductionTensorIso I).hom.naturality _).symm)

theorem adicReductionMap_quasiIso {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    [QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I) φ)] :
    QuasiIso (adicReductionMap I φ) := by
  apply quasiIso_of_arrow_mk_iso
    (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I) φ) _
  refine Arrow.isoMk (adicReductionComplexIso I C) (adicReductionComplexIso I D) ?_
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((adicReductionTensorIso I).hom.naturality (φ.f n)).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicReduction.Construction
