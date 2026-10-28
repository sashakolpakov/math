import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Assembly Total Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyTotalMap

noncomputable section

/-! The original total map of a complex-valued diagram is the same
map as totalizing its assembled presheaf map, also after pullback. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
universe u v s t a b
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

local instance limits : HasLimitsOfSize.{0,0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0,0,max u v,u}
local instance colimits : HasColimitsOfSize.{0,0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v,u,0,0} R

theorem map {P Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ}
    (f : P ⟶ Q) :
    (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map f =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) f) := rfl

theorem refined_map {D : Type a} [Category.{b} D] (r : C ⥤ D)
    {P : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ}
    {Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ}
    (f : r.op ⋙ P ⟶ Q) :
    (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map f =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R E
        (K := ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback R r).mapHomologicalComplex (.up ℕ)).obj
          (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P))
        (L := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q)
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) f) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyTotalMap
