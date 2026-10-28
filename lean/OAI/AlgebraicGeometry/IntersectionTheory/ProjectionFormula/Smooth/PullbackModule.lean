import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChangeSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralAffineSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen

/-! # Pullback Module -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackModule

noncomputable section

/-! The reduced inverse-image support under a smooth morphism with
geometrically integral fibers has the actual base-changed local module
at every point, including nongeneric points of the original support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable {X Y : Scheme} [IsLocallyNoetherian Y] (f : X ⟶ Y) [Smooth f] [GeometricallyIntegral f]
  (B : IrreducibleCloseds Y) (x : X) (hx : f x ∈ (B : Set Y))

include hx in
theorem mem : x ∈ (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B : Set X) := by
  rw [Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_coe]
  exact hx

theorem kernel : (Stalk.PrimeQuotient.kernelPrime Y B (f x) hx).asIdeal.map (f.stalkMap x).hom =
    (Stalk.PrimeQuotient.kernelPrime X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (mem f B x hx)).asIdeal := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨U, V, q, i, j, hU, hV, hq, hgi, hi, hj, hv, hs⟩ := Divisors.LineBundles.Smooth.IntegralAffineSourceCharts.BundleCycles.smoothIntegral_hasAffineSourceCharts f x
  let := hU
  let := hV
  let := hq
  let := hgi
  let := hi
  let := hj
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian i
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  obtain ⟨v, hv⟩ := hv
  have hqv : i (q v) = f x :=
    (congrArg (fun g : V ⟶ Y => g v) hs).trans (congrArg f hv)
  have hb : (i ⁻¹' (B : Set Y)).Nonempty := ⟨q v, by change i (q v) ∈ (B : Set Y); rwa [hqv]⟩
  let B' := Open.SupportDimension.preimage i B hb
  let R := Γ(U, ⊤)
  let S := Γ(V, ⊤)
  let : Algebra R S := q.appTop.hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  let q₀ := Divisors.LineBundles.AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S
  have h₀ : q₀ ≫ U.isoSpec.inv = V.isoSpec.inv ≫ q := Scheme.isoSpec_inv_naturality q
  have hsq : IsPullback q₀ V.isoSpec.inv U.isoSpec.inv q := IsPullback.of_vert_isIso ⟨h₀⟩
  let : Smooth q₀ := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : GeometricallyIntegral q₀ := MorphismProperty.of_isPullback hsq.flip inferInstance
  let i' : Spec (.of R) ⟶ Y := U.isoSpec.inv ≫ i
  let j' : Spec (.of S) ⟶ X := V.isoSpec.inv ≫ j
  have hs' : q₀ ≫ i' = j' ≫ f := by
    change q₀ ≫ U.isoSpec.inv ≫ i = (V.isoSpec.inv ≫ j) ≫ f
    rw [← Category.assoc, h₀, Category.assoc, hs, ← Category.assoc]
  let P : PrimeSpectrum R := U.isoSpec.hom (CycleClass.Thom.IntersectionGeometry.supportPoint B')
  let z : PrimeSpectrum S := V.isoSpec.hom v
  have hP : i' P = CycleClass.Thom.IntersectionGeometry.supportPoint B := by
    have he := congrArg (fun g : U ⟶ U => g (CycleClass.Thom.IntersectionGeometry.supportPoint B')) U.isoSpec.hom_inv_id
    exact (congrArg i he).trans (Open.SupportBaseChangeSquare.preimage_point i B hb)
  have hz : j' z = x := by
    have he := congrArg (fun g : V ⟶ V => g v) V.isoSpec.hom_inv_id
    exact (congrArg j he).trans hv
  have hqz : i' (q₀ z) = f x :=
    (congrArg (fun g : Spec (.of S) ⟶ Y => g z) hs').trans (congrArg f hz)
  have hPz : P.asIdeal.map (algebraMap R S) ≤ z.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply (PrimeSpectrum.le_iff_specializes P (q₀ z)).mpr
    apply i'.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp
    rw [hP, hqz]
    exact (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).specializes hx
  let Q := Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S P
  let A₀ := Affine.SupportStalk.support S Q
  let B₀ := Affine.SupportStalk.support R P
  have hB₀ : i' (CycleClass.Thom.IntersectionGeometry.supportPoint B₀) = CycleClass.Thom.IntersectionGeometry.supportPoint B :=
    (congrArg i' (Affine.SupportStalk.point R P)).trans hP
  have hA₀ : j' (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) := by
    rw [Affine.SupportStalk.point]
    change j' (Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S P) = _
    rw [Divisors.LineBundles.Geometric.AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_eq_fiberGeneric,
      Divisors.LineBundles.Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare f q₀ i' j' hs', hP]
    exact (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_genericPoint f B).symm
  have hzA : z ∈ (A₀ : Set (Spec (.of S))) := Affine.SupportStalk.mem S Q z hPz
  have hzB : q₀ z ∈ (B₀ : Set (Spec (.of R))) :=
    Affine.SupportStalk.mem R P (q₀ z) (Ideal.map_le_iff_le_comap.mp hPz)
  have hloc : (Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) B₀ (q₀ z) hzB).asIdeal.map (q₀.stalkMap z).hom =
      (Stalk.PrimeQuotient.kernelPrime (Spec (.of S)) A₀ z hzA).asIdeal := by
    rw [← Affine.SupportStalk.kernel_map R P (q₀ z) (Ideal.map_le_iff_le_comap.mp hPz),
      ← Affine.SupportStalk.kernel_map S Q z hPz]
    exact Affine.SupportBaseChange.ideal R S (algebraMap R S) P z
  cases hz
  exact Open.SupportBaseChangeSquare.kernel f q₀ i' j' hs'.symm
    (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) B A₀ B₀ hA₀ hB₀ z hzA hzB (mem f B _ hx) hx hloc

def equiv :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (Flat.Extension.baseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)).obj
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (f x) hx) ≃ₗ[X.presheaf.stalk x]
        CycleClass.Thom.IntersectionGeometry.localSupportModule X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (mem f B x hx) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let p := Stalk.PrimeQuotient.kernelPrime Y B (f x) hx
  let q := Stalk.PrimeQuotient.kernelPrime X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (mem f B x hx)
  let eY := Stalk.PrimeQuotient.moduleEquiv Y B (f x) hx p (Stalk.PrimeQuotient.kernelPrime_image Y B (f x) hx)
  let eX := Stalk.PrimeQuotient.moduleEquiv X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (mem f B x hx) q
    (Stalk.PrimeQuotient.kernelPrime_image X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (mem f B x hx))
  exact ((Flat.Extension.baseChange R S).mapIso eY.toModuleIso).toLinearEquiv.trans
    ((Ideal.qoutMapEquivTensorQout (R := R) (I := p.asIdeal) S).symm.trans
      ((Submodule.quotEquivOfEq _ _ (kernel f B x hx)).trans eX.symm))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackModule
