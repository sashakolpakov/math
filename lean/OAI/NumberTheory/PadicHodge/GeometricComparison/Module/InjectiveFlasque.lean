import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover
import Mathlib.Topology.Sheaves.Flasque

/-! # Injective Flasque -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.InjectiveFlasque.ModuleInjectiveFlasque

noncomputable section

/-! Injective module sheaves are flasque, and their actual open restrictions remain flasque. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

theorem flasque [Injective F] : TopCat.Sheaf.IsFlasque F where
  epi {U V} i := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro s
    let a : ModuleCat.of R R ⟶ F.obj.obj V :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton R (F.obj.obj V) s)
    obtain ⟨b, hb⟩ := AlgebraicGeometry.Crystalline.Cohomology.SheafInjective.SheafInjectiveRestrictions.exists_extension
      (Opens.grothendieckTopology X) i.unop (ModuleCat.of R R) F a
    refine ⟨b 1, ?_⟩
    exact (congrArg (fun f => f 1) hb).trans (one_smul R s)

variable {X} {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

theorem restriction [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).obj F) where
  epi {U V} i := by
    change Epi (F.obj.map (f.opensFunctor.map i.unop).op)
    infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.InjectiveFlasque.ModuleInjectiveFlasque
