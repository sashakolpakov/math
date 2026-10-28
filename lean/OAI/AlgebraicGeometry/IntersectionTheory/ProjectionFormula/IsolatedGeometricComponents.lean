import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedPairDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeComponent

/-! # Isolated Geometric Components -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents

noncomputable section

/-! The nonclosed local primes of an isolated parameter intersection
are actual global irreducible components of the intersection support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing

variable (Z : Scheme) [IsLocallyNoetherian Z] (A B : IrreducibleCloseds Z)
  (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))

def intersection : Closeds Z := ⟨(A : Set Z) ∩ (B : Set Z), A.isClosed.inter B.isClosed⟩

theorem exists_component (r : Z.presheaf.stalk x) (hrm : r ∈ maximalIdeal (Z.presheaf.stalk x))
    (hisolated : (Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) ∩
      Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) ∩
      Module.support (Z.presheaf.stalk x) ((Z.presheaf.stalk x) ⧸ Ideal.span {r}) ⊆
        {closedPoint (Z.presheaf.stalk x)})
    (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hpA : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))
    (hpB : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB))
    (hne : p ≠ closedPoint (Z.presheaf.stalk x)) :
    ∃ D : irreducibleComponents (intersection Z A B),
      CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z (intersection Z A B) D = Stalk.DivisorSupport.primeClosure Z x p := by
  let : Module.Finite (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) :=
    Local.TorFinite.localSupportModule_finite Z A x hxA
  let : Module.Finite (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) :=
    Local.TorFinite.localSupportModule_finite Z B x hxB
  apply Local.PrimeComponent.exists_component Z (intersection Z A B) x p
    ⟨Local.SupportSpectrum.image_mem_support Z A x hxA p hpA,
      Local.SupportSpectrum.image_mem_support Z B x hxB p hpB⟩
  intro q hq hqp
  exact IsolatedPairDimension.minimal (Z.presheaf.stalk x)
    (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) r hisolated hrm
      p ⟨hpA, hpB⟩ hne q
      ⟨(GeometricSupportLocalization.mem_iff Z A x hxA q).mpr hq.1,
        (GeometricSupportLocalization.mem_iff Z B x hxB q).mpr hq.2⟩ hqp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents
