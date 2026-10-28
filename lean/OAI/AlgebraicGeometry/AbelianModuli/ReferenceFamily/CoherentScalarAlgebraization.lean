import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentLineGenerators
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Coherent Scalar Algebraization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentScalarAlgebraization

noncomputable section

section

/-! Actual native holomorphic scalar maps from finite-type quasicoherent
algebraic modules have unique algebraic realizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem coherent_holomorphicScalarFunctional_algebraic (M : V.carrier.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (f : Holomorphic.FunctionalNe.HolomorphicScalarFunctional V M) :
    ∃ g : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier, Holomorphic.FunctionalNe.holomorphicScalarFunctionalOfAlgebraic V g = f := by
  obtain ⟨I, hI, L, s, hs⟩ := CoherentLineGenerators.coherent_hasFiniteLineGenerators V M
  let : Fintype I := hI
  let : Epi (CategoryTheory.Limits.Sigma.desc s) := hs
  exact Holomorphic.FunctionalDescent.exists_algebraic_scalarFunctional_of_line_generators V M (fun _ : I => L) s f

def nativeScalarAnalytification {M : V.carrier.Modules} (f : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) :
    (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj M ⟶
      SheafOfModules.unit (DivisorClass.Chern.HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace) :=
  (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map f ≫ (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso V).hom

theorem nativeScalarAnalytification_adjoint {M : V.carrier.Modules} (f : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) :
    (DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv _ _ (nativeScalarAnalytification V f) =
      Holomorphic.FunctionalNe.holomorphicScalarFunctionalOfAlgebraic V f := by
  exact ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv_naturality_left f
    (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso V).hom).trans
      (congrArg (f ≫ ·) (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso_normalization V))

theorem nativeScalarAnalytification_injective (M : V.carrier.Modules) :
    Function.Injective (nativeScalarAnalytification V (M := M)) := by
  intro f g he
  apply Holomorphic.FunctionalDescent.holomorphicScalarFunctionalOfAlgebraic_injective V M
  exact (nativeScalarAnalytification_adjoint V f).symm.trans
    ((congrArg ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv _ _) he).trans
      (nativeScalarAnalytification_adjoint V g))

theorem nativeScalarAnalytification_surjective (M : V.carrier.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Function.Surjective (nativeScalarAnalytification V (M := M)) := by
  intro f
  obtain ⟨g, hg⟩ := coherent_holomorphicScalarFunctional_algebraic V M
    ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv _ _ f)
  exact ⟨g, ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleAnalytificationAdjunction V).homEquiv _ _).injective
    ((nativeScalarAnalytification_adjoint V g).trans hg)⟩

def coherentNativeScalarEquiv (M : V.carrier.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) ≃
      ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj M ⟶
        SheafOfModules.unit (DivisorClass.Chern.HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace)) :=
  Equiv.ofBijective (nativeScalarAnalytification V)
    ⟨nativeScalarAnalytification_injective V M, nativeScalarAnalytification_surjective V M⟩

end

/-! A native holomorphic retraction onto the original structure module
of a coherent algebraic sheaf is an actual algebraic retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem native_retraction_algebraic (M : V.carrier.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (i : HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ M)
    (r : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj M ⟶
      (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj (HilbertConstruction.Line.Bundles.structureModule V.carrier))
    (hr : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map i ≫ r = 𝟙 _) :
    ∃ g : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier,
      (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map g = r ∧ i ≫ g = 𝟙 _ := by
  obtain ⟨g, hg⟩ := nativeScalarAnalytification_surjective V M
    (r ≫ (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso V).hom)
  have he : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map g = r :=
    (cancel_mono (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso V).hom).mp hg
  refine ⟨g, he, ?_⟩
  apply nativeScalarAnalytification_injective V (HilbertConstruction.Line.Bundles.structureModule V.carrier)
  unfold nativeScalarAnalytification
  rw [Functor.map_comp, he, hr]
  exact (congrArg (· ≫ (DivisorClass.Chern.Holomorphic.AnalytificationUnit.holomorphicAnalytificationUnitIso V).hom)
    ((DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map_id (HilbertConstruction.Line.Bundles.structureModule V.carrier))).symm

theorem native_split_extension_algebraic (M N : V.carrier.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (i : HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ M) (p : M ⟶ N) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (r : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj M ⟶
      (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).obj (HilbertConstruction.Line.Bundles.structureModule V.carrier))
    (hr : (DivisorClass.Chern.Holomorphic.ModuleAnalytification.algebraicModuleHolomorphicAnalytification V).map i ≫ r = 𝟙 _) :
    Nonempty (ShortComplex.mk i p hip).Splitting := by
  obtain ⟨g, _, hg⟩ := native_retraction_algebraic V M i r hr
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction (ShortComplex.mk i p hip)
    hS.exact g hg hS.epi_g⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentScalarAlgebraization
