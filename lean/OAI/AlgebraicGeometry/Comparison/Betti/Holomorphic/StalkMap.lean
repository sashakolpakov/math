import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGerms
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Stalk Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkMap.AnalyticLocal

noncomputable section

/-! The actual sheaf stalk maps to the holomorphic germ ring through
the colimit of its section-to-germ maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicGermCocone (x : E) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of E) x).op ⋙ FunctionSheaf.holomorphicFunctionPresheaf E) where
  pt := CommRingCat.of (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)
  ι :=
    { app := fun U => CommRingCat.ofHom (SectionGerms.AnalyticLocal.holomorphicSectionGerm U.unop.val x U.unop.property)
      naturality := by
        intro U V f
        change CommRingCat.ofHom ((SectionGerms.AnalyticLocal.holomorphicSectionGerm V.unop.val x V.unop.property).comp
          (Restrictions.holomorphicFunctionRestrict (leOfHom f.unop)).toRingHom) =
            CommRingCat.ofHom (SectionGerms.AnalyticLocal.holomorphicSectionGerm U.unop.val x U.unop.property)
        exact congrArg CommRingCat.ofHom
          (SectionGerms.AnalyticLocal.holomorphicSectionGerm_restrict (leOfHom f.unop) x V.unop.property) }

def holomorphicStalkToGerm (x : E) : (FunctionSheaf.holomorphicFunctionPresheaf E).stalk x →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  (colimit.desc _ (holomorphicGermCocone E x)).hom

theorem holomorphicStalkToGerm_germ (x : E) (U : Opens E) (hx : x ∈ U) :
    (holomorphicStalkToGerm E x).comp ((FunctionSheaf.holomorphicFunctionPresheaf E).germ U x hx).hom =
      SectionGerms.AnalyticLocal.holomorphicSectionGerm U x hx := by
  exact congrArg CommRingCat.Hom.hom (colimit.ι_desc (holomorphicGermCocone E x) (op ⟨U, hx⟩))

theorem holomorphicStalkToGerm_germ_apply (x : E) (U : Opens E) (hx : x ∈ U)
    (f : FunctionPure.holomorphicFunctions U) :
    holomorphicStalkToGerm E x ((FunctionSheaf.holomorphicFunctionPresheaf E).germ U x hx f) =
      SectionGerms.AnalyticLocal.holomorphicSectionGerm U x hx f := DFunLike.congr_fun (holomorphicStalkToGerm_germ E x U hx) f

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkMap.AnalyticLocal
