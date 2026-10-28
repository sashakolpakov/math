import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar

/-! # Ideal Scalar Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarNaturality.ModuleIdealScalarNaturality

noncomputable section

/-! Scalar extension commutes naturally with coefficient-ideal quotients of full complexes. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

abbrev scalarFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S := NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S

def source : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  scalarFunctor R S ⋙ NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor S (I.map (algebraMap R S))

def target : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I ⋙ scalarFunctor R S

def component (M : ModuleCat.{u} R) : (source R S I).obj M ≅ (target R S I).obj M :=
  (IdealScalarChange.ModuleIdealScalarChange.equiv R S M I).toModuleIso

theorem natural {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (source R S I).map f ≫ (component R S I N).hom =
      (component R S I M).hom ≫ (target R S I).map f := by
  let : Module R ((target R S I).obj N) := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S ((target R S I).obj N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply ModuleCat.hom_ext
  let qM := ((I.map (algebraMap R S)) • (⊤ : Submodule S (S ⊗[R] M))).mkQ
  have hlin : (((source R S I).map f ≫ (component R S I N).hom).hom).comp qM =
      (((component R S I M).hom ≫ (target R S I).map f).hom).comp qM := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s m
    change IdealScalarChange.ModuleIdealScalarChange.equiv R S N I (Submodule.Quotient.mk (s ⊗ₜ[R] f m)) =
      (((NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I).map f).hom.baseChange S)
        (IdealScalarChange.ModuleIdealScalarChange.equiv R S M I (Submodule.Quotient.mk (s ⊗ₜ[R] m)))
    rw [IdealScalarChange.ModuleIdealScalarChange.equiv_mk_tmul, IdealScalarChange.ModuleIdealScalarChange.equiv_mk_tmul]
    erw [LinearMap.baseChange_tmul]
    rfl
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := ((I.map (algebraMap R S)) • (⊤ : Submodule S (S ⊗[R] M))).mkQ_surjective x
  exact LinearMap.congr_fun hlin y

def iso : source R S I ≅ target R S I :=
  NatIso.ofComponents (component R S I) (fun {_ _} f => natural R S I f)

def complexIso (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.complex S (I.map (algebraMap R S))
      (((scalarFunctor R S).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((scalarFunctor R S).mapHomologicalComplex (.up ℕ)).obj (NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.complex R I K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => component R S I (K.X n))
    (fun n m _ => (natural R S I (K.d n m)).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarNaturality.ModuleIdealScalarNaturality
