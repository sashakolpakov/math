import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralAffineSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen

/-! # Fiber Grading -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGrading

noncomputable section

/-! The generic point of a geometrically integral smooth fiber preserves
the actual point codimension, including over singular target schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

theorem affine_coheight {E X : Scheme.{0}} [IsAffine E] [IsAffine X]
    [IsLocallyNoetherian E] [IsLocallyNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p] (x : X) :
    coheight (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x) = coheight x := by
  let R := Γ(X, ⊤)
  let S := Γ(E, ⊤)
  let : Algebra R S := p.appTop.hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E⟩
  let q := Divisors.LineBundles.AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S
  have hs : IsPullback q E.isoSpec.inv X.isoSpec.inv p :=
    IsPullback.of_vert_isIso ⟨Scheme.isoSpec_inv_naturality p⟩
  let : Smooth q := MorphismProperty.of_isPullback hs.flip inferInstance
  let : GeometricallyIntegral q := MorphismProperty.of_isPullback hs.flip inferInstance
  let y := X.isoSpec.hom x
  have hy : X.isoSpec.inv y = x := by
    exact congrArg (fun h : X ⟶ X => h x) X.isoSpec.hom_inv_id
  have he := Divisors.LineBundles.Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q X.isoSpec.inv E.isoSpec.inv hs.w y
  have he' := he.trans (congrArg (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) hy)
  calc
    coheight (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x) =
        coheight (E.isoSpec.inv (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint q y)) := congrArg Order.coheight he'.symm
    _ = coheight (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint q y) := coheight_eq_of_isOpenImmersion E.isoSpec.inv
    _ = coheight (Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S y) :=
      congrArg Order.coheight (Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_eq_fiberGeneric R S y).symm
    _ = coheight y := Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_coheight R S y
    _ = coheight (X.isoSpec.inv y) := (coheight_eq_of_isOpenImmersion X.isoSpec.inv).symm
    _ = coheight x := congrArg Order.coheight hy

theorem coheight {E X : Scheme.{0}}
    [IsLocallyNoetherian E] [IsLocallyNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p] (x : X) :
    Order.coheight (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x) = Order.coheight x := by
  obtain ⟨U, V, q, i, j, hU, hV, hq, hgi, hi, hj, hz, hs⟩ :=
    Divisors.LineBundles.Smooth.IntegralAffineSourceCharts.BundleCycles.smoothIntegral_hasAffineSourceCharts p (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)
  let := hU
  let := hV
  let := hq
  let := hgi
  let := hi
  let := hj
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian i
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  obtain ⟨z, hz⟩ := hz
  have hx : i (q z) = x :=
    (congrArg (fun h : V ⟶ X => h z) hs).trans
      ((congrArg p hz).trans (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
  have he := Divisors.LineBundles.Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q i j hs (q z)
  rw [hx] at he
  rw [← he, coheight_eq_of_isOpenImmersion j, affine_coheight q,
    ← coheight_eq_of_isOpenImmersion i, hx]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGrading
