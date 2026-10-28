import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackHomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainAdjunctionTranspose
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Cech Base Tmul -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul

noncomputable section

/-! The canonical tensor comparison for ordered Cech complexes in a commuting
square of schemes. Cartesianity is needed for the later isomorphism theorem. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev target := SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i)

def restrictedMap : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U ⟶
    ((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (target f ρ M U) :=
  CechPullbackHomology.Construction.CechPullbackMap.map f π M U ≫
    eqToHom (congrArg (fun p => SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex p ((Scheme.Modules.pullback f).obj M)
      (fun i => f ⁻¹ᵁ U i)) h) ≫
    (CechScalarCoface.Construction.CechScalarRestriction.complexIso ρ g ((Scheme.Modules.pullback f).obj M)
      (fun i => f ⁻¹ᵁ U i)).hom

def map :
    ((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) ⟶ target f ρ M U :=
  CochainAdjunctionTranspose.Construction.CochainAdjunction.transpose (ModuleCat.extendRestrictScalarsAdj g.appTop.hom)
    (restrictedMap f π ρ g h M U)

theorem one_tmul (q : ℕ) (s : (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X q) :
    (map f π ρ g h M U).f q ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      (restrictedMap f π ρ g h M U).f q s :=
  ConcreteCategory.congr_hom (CochainAdjunctionTranspose.Construction.CochainAdjunction.transpose_component
    (ModuleCat.extendRestrictScalarsAdj g.appTop.hom) (restrictedMap f π ρ g h M U) q) s

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul
