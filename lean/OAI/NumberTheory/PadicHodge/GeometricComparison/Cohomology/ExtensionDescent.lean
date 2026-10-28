import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionSheaf
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections

/-! # Extension Descent -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

noncomputable section

/-! A coefficient map kills an actual degree-one class when it kills the difference of local lifts on a covering overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction

universe u
variable {X : Scheme.{u}} {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  (E : ExtensionOf.CohomologyExtension.Extension X F) (f : F ⟶ G)

theorem ExtensionOf.CohomologyExtension.Extension.class_map_eq_zero_of_overlap {U D : X.ProEt}
    (g : U ⟶ ⊤_ X.ProEt) [Surjective g.left] [QuasiCompact g.left]
    (a b : D ⟶ U) (h : IsPullback a.left b.left g.left g.left)
    (s : E.Fiber U) (c : F.obj.obj (op D))
    (hc : E.inclusion.hom.app (op D) c + (E.restrict a s).val = (E.restrict b s).val)
    (hz : f.hom.app (op D) c = 0) : Sheaf.H.map f 1 E.extClass = 0 := by
  have he : (E.map f).restrict a (E.mapFiber f U s) =
      (E.map f).restrict b (E.mapFiber f U s) := by
    rw [E.mapFiber_restrict, E.mapFiber_restrict]
    exact E.mapFiber_eq_of_difference f D (E.restrict a s) (E.restrict b s) c hc hz
  obtain ⟨t, _, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback
    (E.map f).fiberSheaf g a b h (E.mapFiber f U s) he
  rw [← E.map_extClass f]
  exact (E.map f).class_eq_zero_iff_fiber_nonempty.mpr ⟨t⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology
