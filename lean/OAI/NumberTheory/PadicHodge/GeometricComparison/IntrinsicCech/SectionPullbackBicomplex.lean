import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinatePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafPullbackAdjoint

/-! # Section Pullback Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex

noncomputable section

/-! The native section-bicomplex pullback is the original direct Čech pullback under the actual global-section isomorphism. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := Instances.IntrinsicCechInstances.hasCoproducts R Y.left
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

def map {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ} {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    SectionsTotal.IntrinsicCechSectionsTotal.bicomplex R Y.left U K ⟶ SectionsTotal.IntrinsicCechSectionsTotal.bicomplex R X.left V L :=
  Finite.TotalTransformation.FiniteTotalTransformation.bicomplexMap (Intrinsic.SectionCochainAdjoint.IntrinsicSectionPullback.map f) (Bicomplex.IntrinsicCechBicomplex.bicomplex R Y.left U K) ≫
    Finite.TotalIso.FiniteTotalNaturality.map (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left))
      (PullbackNormalization.IntrinsicCechPullback.bicomplexMap f U V r hr b)

theorem row_map {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ} {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) (q : ℕ) :
    (map f U V r hr b).f q = GlobalPullback.IntrinsicCechGlobalPullback.sectionsMap R f U V r hr (K.X q) (L.X q) (b.f q) := rfl

theorem deRham_square : map f U V r hr (DeRham.Int.sheafPullback f) ≫
      (CechBicomplex.IntrinsicCechBicomplex.sectionIso R X V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).hom =
    (CechBicomplex.IntrinsicCechBicomplex.sectionIso R Y U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)).hom ≫
      CoordinatePullback.IntrinsicCechCoordinatePullback.sheafMap R f U V r hr := by
  apply HomologicalComplex.Hom.ext
  funext q
  let P := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X q
  let Q := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X q
  have h := GlobalPullback.IntrinsicCechGlobalPullback.naturality R f U V r hr P Q ((DeRham.Int.sheafPullback f).f q)
  have hc := congrArg (fun a => a.hom) (DeRham.SheafPullbackAdjoint.sheafPullback_adjoint f q)
  exact h.trans (congrArg (fun a => (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app P ≫
    Cech.CechPullback.map R f.left U V r hr a) hc)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackBicomplex.IntrinsicCechSectionPullbackBicomplex
