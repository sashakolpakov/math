import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAdjunctionEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts

/-! # Cech Tensor Products -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTensorProducts

noncomputable section

/-! Finite ordered Cech base change is invertible when its intersection-factor maps are. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)

theorem component_isIso (q : ℕ)
    [∀ i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q, IsIso (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h M U q i)] :
    IsIso ((CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U).f q) := by
  have : Finite (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :=
    inferInstanceAs (Finite {i : Fin (q + 1) → ι // StrictMono i})
  let P := fun i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1
  let Q := fun i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1
  have : IsIso (piComparison (ModuleCat.extendScalars g.appTop.hom) P) :=
    TensorProducts.Construction.FiniteTensorProducts.comparison_isIso g.appTop.hom P
  have (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : IsIso
      (((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv (P i) (Q i)).symm
        (CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q i)) :=
    inferInstanceAs (IsIso (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h M U q i))
  exact ProductAdjunctionEq.Construction.ProductAdjunction.isIso_transpose (ModuleCat.extendRestrictScalarsAdj g.appTop.hom)
    P Q ((CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f q) (CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q)
    (CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g h M U q)

theorem isIso_of_factors
    [∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsIso (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h M U q i)] :
    IsIso (CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U) := by
  have (q : ℕ) : IsIso ((CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U).f q) := component_isIso f π ρ g h M U q
  exact HomologicalComplex.Hom.isIso_of_components _

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTensorProducts
