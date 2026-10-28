import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Base Open Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction

noncomputable section

/-! Actual sections on an open subset, with scalars from the global sections of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

universe u

def baseOpenScalarMap {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) :
    Γ(S, ⊤) →+* Γ(X, U) :=
  (π.appLE ⊤ U (by simp)).hom

theorem baseOpenScalarMap_eq {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) :
    baseOpenScalarMap π U =
      (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp π.appTop.hom := rfl

@[instance_reducible]
def baseOpenSectionsAlgebra {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) :
    Algebra Γ(S, ⊤) Γ(X, U) := (baseOpenScalarMap π U).toAlgebra

@[instance_reducible]
def baseOpenSectionsModule {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    Module Γ(S, ⊤) Γ(M, U) := Module.compHom Γ(M, U) (baseOpenScalarMap π U)

def baseOpenSectionsFunctor {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) where
  obj M := letI := baseOpenSectionsModule π M U; ModuleCat.of Γ(S, ⊤) Γ(M, U)
  map {M N} q := by
    letI := baseOpenSectionsModule π M U
    letI := baseOpenSectionsModule π N U
    exact ModuleCat.ofHom
      { (q.val.app (.op U)).hom.toAddMonoidHom with
        map_smul' := fun r x => (q.val.app (.op U)).hom.map_smul (baseOpenScalarMap π U r) x }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def baseOpenSectionsRestriction {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj M →ₗ[Γ(S, ⊤)] (baseOpenSectionsFunctor π U).obj M where
  toFun := M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  map_add' := (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_add
  map_smul' r x := (M.val.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_smul (π.appTop r) x

theorem baseOpenScalarMap_pullback {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    (f.app U).hom.comp (baseOpenScalarMap π U) =
      baseOpenScalarMap (f ≫ π) (f ⁻¹ᵁ U) := by
  have h := Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) (by simp) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  exact congrArg CommRingCat.Hom.hom h

def baseOpenSectionsPullbackAlgHom {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    letI := baseOpenSectionsAlgebra π U
    letI := baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
    Γ(Y, U) →ₐ[Γ(S, ⊤)] Γ(X, f ⁻¹ᵁ U) :=
  letI := baseOpenSectionsAlgebra π U
  letI := baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
  { (f.app U).hom with
    commutes' r := RingHom.congr_fun (baseOpenScalarMap_pullback f π U) r }

local instance baseOpenSectionTensor (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def tensorSectionGlobalCoefficientLinear {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {P : X.Modules} (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (M ⊗ P) →ₗ[Γ(S, ⊤)]
      (baseOpenSectionsFunctor π U).obj M := by
  letI := baseOpenSectionsModule π M U
  letI := baseOpenSectionsModule π (M ⊗ P) U
  let e : (baseOpenSectionsFunctor π U).obj (M ⊗ P) ≃ₗ[Γ(S, ⊤)]
      (baseOpenSectionsFunctor π U).obj M :=
    { (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).symm.toAddEquiv with
      map_smul' := fun r x => (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv M a U).symm.map_smul
        (baseOpenScalarMap π U r) x }
  exact e.toLinearMap.comp (baseOpenSectionsRestriction π (M ⊗ P) U)

theorem tensorSectionGlobalCoefficientLinear_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {P : X.Modules} (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)]
    (x : (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (M ⊗ P)) :
    tensorSectionGlobalCoefficientLinear π M a U x = TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient M a U x := rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction
