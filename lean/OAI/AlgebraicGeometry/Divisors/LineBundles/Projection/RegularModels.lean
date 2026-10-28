import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates

/-! # Regular Models -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularModels.BundleCycles

noncomputable section

/-! The genuine regular support model has the dimension sum required
for the product Thom comparison, with norm-preserving complex coordinates. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "F" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem projectionRegularModel_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Z C).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom +
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B).hom := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq, SupportDimension.BundleCycles.projectionIrreducibleSupport_dimension,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]

def finiteProductCoordinatesForDimension (d c n : ℕ) (h : d + c = n) :
    ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin n → ℂ) := h ▸ CycleClass.Thom.Finite.ProductCoordinates.Constructions.finiteProductCoordinates d c

theorem finiteProductCoordinatesForDimension_norm (d c n : ℕ) (h : d + c = n)
    (v : (Fin d → ℂ) × (Fin c → ℂ)) : ‖finiteProductCoordinatesForDimension d c n h v‖ = ‖v‖ := by
  subst n
  exact CycleClass.Thom.Finite.ProductCoordinates.Constructions.finiteProductCoordinates_norm d c v

def projectionRegularModelCoordinates : (F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) ≃L[ℂ] CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Z C :=
  finiteProductCoordinatesForDimension _ _ _ (projectionRegularModel_dimension X Y B Z πX πY hprod).symm

theorem projectionRegularModelCoordinates_norm (v : F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) :
    ‖projectionRegularModelCoordinates X Y B Z πX πY hprod v‖ = ‖v‖ :=
  finiteProductCoordinatesForDimension_norm _ _ _ _ v

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularModels.BundleCycles
