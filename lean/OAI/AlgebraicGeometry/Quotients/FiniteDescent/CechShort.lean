import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechLowDegreeDifferentials
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechShortComplex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule

/-! # Cech Short -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort

noncomputable section

/-! The first three terms of the native Cech complex are the ordinary
section-coordinate short complex, with both differentials identified. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechShortCoordinates

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

abbrev source := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).sc' 0 1 2
abbrev target := OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U

def zero : (source π M U).X₁ ≅ (target π M U).X₁ :=
  (CechTuplePi.Construction.CechTupleCoordinates.zero π M U).toModuleIso

def one : (source π M U).X₂ ≅ (target π M U).X₂ :=
  (CechTuplePi.Construction.CechTupleCoordinates.one π M U).toModuleIso

def two : (source π M U).X₃ ≅ (target π M U).X₃ :=
  (CechTuplePi.Construction.CechTupleCoordinates.two π M U).toModuleIso

theorem first : (source π M U).f ≫ (one π M U).hom =
    (zero π M U).hom ≫ (target π M U).f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change CechTuplePi.Construction.CechTupleCoordinates.one π M U ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1 z) =
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U (CechTuplePi.Construction.CechTupleCoordinates.zero π M U z)
  funext i j
  exact CechLowDegreeDifferentials.Construction.CechTupleCoordinates.differential_zero π M U z i j

theorem second : (source π M U).g ≫ (two π M U).hom =
    (one π M U).hom ≫ (target π M U).g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change CechTuplePi.Construction.CechTupleCoordinates.two π M U ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 1 2 z) =
    OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (BaseModule.Construction.BaseModuleSheaf.sheaf π M) U (CechTuplePi.Construction.CechTupleCoordinates.one π M U z)
  funext i j k
  exact CechLowDegreeDifferentials.Construction.CechTupleCoordinates.differential_one π M U z i j k

def iso : source π M U ≅ target π M U :=
  ShortComplex.isoMk (zero π M U) (one π M U) (two π M U)
    (first π M U).symm (second π M U).symm

end Construction.CechShortCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort
