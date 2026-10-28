import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen

/-! # Polarization Open Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PolarizationOpenCharts

noncomputable section

/-! The constructed affine rational-polarization parameters are actual
charts of the original normalized graph-power subfunctor. Their lifting
criterion is identified using the native iterated-base-change comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme} (M : Over B) {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (q : M.left ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

def rationalNormalizedGraphPowerOpenChart
    {R : Type} [CommRing R] [IsNoetherianRing R] (i : Spec (.of R) ⟶ M.left)
    (hLi : (L.pullback (pullback.fst F.abelian.scheme.hom i)).IsAmple) :
    SubfunctorOpen.SubfunctorOpenChart
      (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d) i := by
  let A := F.abelian.pullback i
  let Li := L.pullback (pullback.fst F.abelian.scheme.hom i)
  let Z := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A (P.baseChange i) Li
    (i ≫ q) hLi d hd δ hδ
  refine
    { parameter := Z
      mono := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter_mono A
        (P.baseChange i) Li (i ≫ q) hLi d hd δ hδ
      locallyFiniteType := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter_locallyOfFiniteType A
        (P.baseChange i) Li (i ≫ q) hLi d hd δ hδ
      quasiCompact := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter_quasiCompact A
        (P.baseChange i) Li (i ≫ q) hLi d hd δ hδ
      lifts := ?_ }
  intro T a
  have hc : (a ≫ i) ∈ (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor
      (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d)).obj (.op T) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ ((F.pullback i).pullback a)
        ((A.zeroNormalizedBundle Li).pullback (pullback.fst A.scheme.hom a)) d) :=
    GraphPower.EnhancementRestriction.normalizedGraphPowerEnhancement_baseChange_comp_iff δ F L d i a
  have hp : Nonempty (Over.mk a ⟶ Z) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ ((F.pullback i).pullback a)
        ((A.zeroNormalizedBundle Li).pullback (pullback.fst A.scheme.hom a)) d) :=
    ProjectivePolarizationIntrinsic.RationalProjectivePolarizationLocus.parameter_hasPoint_iff_graphPowerEnhancement
      A (P.baseChange i) Li (i ≫ q) hLi d hd δ hδ (F.level.pullback i) (Over.mk a)
  constructor
  · intro h
    obtain ⟨z⟩ := hp.mpr (hc.mp h)
    exact ⟨z.left, z.w⟩
  · rintro ⟨z, hz⟩
    exact hc.mpr (hp.mp ⟨Over.homMk z hz⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PolarizationOpenCharts
