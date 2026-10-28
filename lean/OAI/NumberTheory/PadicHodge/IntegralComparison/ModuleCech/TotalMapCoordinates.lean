import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Total Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapCoordinates

noncomputable section

/-! Module-valued Čech total maps in named cone-total coordinates.
The homology identity is proved before choosing the coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

local instance total_exists (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def total (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U K).total (.up ℕ)

variable {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L)

def map : TotalMapCoordinates.total R U K ⟶ TotalMapCoordinates.total R U L :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a

theorem map_eq : map R U a =
    AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a := rfl

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

theorem homology_map (q : ℕ) :
    homologyMap (map R U a) q =
      homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q := rfl

theorem composition (q : ℕ) {T : ModuleCat.{max u v} R}
    (b : (TotalMapCoordinates.total R U L).homology q ⟶ T) :
    homologyMap (map R U a) q ≫ b =
      homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q ≫ b := by
  rw [homology_map]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapCoordinates
