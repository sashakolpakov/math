import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.StalkIdeal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedEtaleSupport

/-! # Local Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.LocalMultiplicity

noncomputable section

/-! The actual projective cone has native Tor intersection
coefficient one against an integral closed embedded scheme wherever
the chosen projection is etale. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) {Z : Scheme} [IsIntegral Z]
  (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion i]
  (hi : ∀ z, i z ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))

def lift : Z ⟶ (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).toScheme :=
  Projective.ProjectionRestriction.lift (Projective.ConeSupport.coordinates L) i hi

omit [IsIntegral Z] [IsClosedImmersion i] in
theorem lift_fac : lift L i hi ≫ (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι = i :=
  Projective.ProjectionRestriction.lift_fac (Projective.ConeSupport.coordinates L) i hi

instance lift_closed : IsClosedImmersion (lift L i hi) := by
  have hc : IsClosedImmersion (lift L i hi ≫ (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι) := (lift_fac L i hi).symm ▸ inferInstance
  let := hc
  exact IsClosedImmersion.of_comp (lift L i hi) (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι

theorem euler_one
    (U : Z.Opens) [Etale (U.ι ≫ Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi)]
    (z : Z) (hz : z ∈ U)
    (hA : i z ∈ (Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z) :
      Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))
    (hB : i z ∈ (Closed.ImmersionSupport.support i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) (d : ℕ) :
    (∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ k *
      (CycleClass.Thom.IntersectionGeometry.localTorLength (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
        (Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z))
        (Closed.ImmersionSupport.support i) (i z) hA hB k).toNat) = 1 := by
  let j := (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι
  let f := Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)
  let η := Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z
  let a := StalkIdeal.onDomain L hL η
  let b := Closed.ImmersionSupport.support (lift L i hi)
  let x := lift L i hi z
  have hpoint : j x = i z := congrArg (fun g : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n => g z) (lift_fac L i hi)
  have hxa : x ∈ (a : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))) := StalkIdeal.mem_of_map L hL η x rfl
  have hxb : x ∈ (b : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))) := by
    change x ∈ (CycleClass.Geometric.StratumClosure.integralImageClosure (lift L i hi) : Set (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)))
    rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
    exact subset_closure (Set.mem_range_self z)
  have hgena : j (CycleClass.Thom.IntersectionGeometry.supportPoint a) = CycleClass.Thom.IntersectionGeometry.supportPoint (Projective.ConeSupport.support L hL η) := StalkIdeal.generic_image L hL η
  have hgenb : j (CycleClass.Thom.IntersectionGeometry.supportPoint b) = CycleClass.Thom.IntersectionGeometry.supportPoint (Closed.ImmersionSupport.support i) := by
    rw [Closed.ImmersionSupport.support_point, Closed.ImmersionSupport.support_point]
    exact congrArg (fun g : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n => g (genericPoint Z)) (lift_fac L i hi)
  have ha' : j x ∈ (Projective.ConeSupport.support L hL η : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := hpoint.symm ▸ hA
  have hb' : j x ∈ (Closed.ImmersionSupport.support i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := hpoint.symm ▸ hB
  have he (k : ℕ) : CycleClass.Thom.IntersectionGeometry.localTorLength (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) a b x hxa hxb k =
      CycleClass.Thom.IntersectionGeometry.localTorLength (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Projective.ConeSupport.support L hL η) (Closed.ImmersionSupport.support i) (i z) hA hB k :=
    (Open.SupportTor.localTorLength_eq j a b (Projective.ConeSupport.support L hL η) (Closed.ImmersionSupport.support i)
      hgena hgenb x hxa hxb ha' hb' k).trans
      (Open.SupportTor.localTorLength_congr_point _ _ _ hpoint ha' hb' hA hB k)
  change (∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ k *
    (CycleClass.Thom.IntersectionGeometry.localTorLength (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Projective.ConeSupport.support L hL η) (Closed.ImmersionSupport.support i)
      (i z) hA hB k).toNat) = 1
  simp_rw [← he]
  let : SmoothOfRelativeDimension (n - m) f := IndependentSmooth.Projection.smooth L hL
  let : Smooth f := SmoothOfRelativeDimension.smooth (n - m) f
  let : Etale (U.ι ≫ (lift L i hi ≫ f)) := by
    change Etale (U.ι ≫ Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi)
    infer_instance
  apply ProjectionFormula.Smooth.FiberMultiplicity.euler_one f a b x hxa hxb
  · exact (congrArg f (StalkIdeal.generic_point L hL η)).trans (Generic.Projection.map_point L hL η)
  · intro y hy
    exact StalkIdeal.mem_of_map L hL η y hy
  · exact EmbeddedEtaleSupport.stalk_properties (lift L i hi) f U z hz hxb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.LocalMultiplicity
