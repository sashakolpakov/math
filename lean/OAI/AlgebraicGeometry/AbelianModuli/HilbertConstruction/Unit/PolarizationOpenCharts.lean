import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen

/-! # Polarization Open Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationOpenCharts

noncomputable section

/-! A supplied actual dual and its etale inducing isogeny give a chart of
the original normalized graph-power subfunctor when twice the exponent
is invertible. The lifting criterion retains all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme} (M : Over B) {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

def unitNormalizedGraphPowerOpenChart
    {R : Type} [CommRing R] [IsNoetherianRing R] (i : Spec (.of R) ⟶ M.left)
    (hLi : (L.pullback (pullback.fst F.abelian.scheme.hom i)).IsAmple)
    (D : Dual.Data.DualAbelianData (F.abelian.pullback i))
    (m : Abelian.Schemes.AbelianScheme.Isogeny (F.abelian.pullback i) D.abelian) [Etale m.hom.left]
    (hunit : IsUnit ((2 * d : ℕ) : Γ(Spec (.of R), ⊤)))
    (recover : (D.poincare.pullback (m.hom ⊗ₘ 𝟙 (F.abelian.pullback i).scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (F.abelian.pullback i)
        (L.pullback (pullback.fst F.abelian.scheme.hom i))).sheaf) :
    SubfunctorOpen.SubfunctorOpenChart
      (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d) i := by
  let A := F.abelian.pullback i
  let Li := L.pullback (pullback.fst F.abelian.scheme.hom i)
  let Z := PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit (P.baseChange i) Li δ hδ
  refine
    { parameter := Z
      mono := PolarizationParameter.UnitPolarizationLocus.parameter_mono D m d hunit (P.baseChange i) Li δ hδ
      locallyFiniteType := PolarizationParameter.UnitPolarizationLocus.parameter_locallyOfFiniteType
        D m d hunit (P.baseChange i) Li δ hδ
      quasiCompact := PolarizationParameter.UnitPolarizationLocus.parameter_quasiCompact D m d hunit (P.baseChange i) Li δ hδ
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
    PolarizationIntrinsic.UnitPolarizationLocus.parameter_hasPoint_iff_graphPowerEnhancement
      D m d hunit (P.baseChange i) Li δ hδ hd hLi recover (F.level.pullback i) (Over.mk a)
  constructor
  · intro h
    obtain ⟨z⟩ := hp.mpr (hc.mp h)
    exact ⟨z.left, z.w⟩
  · rintro ⟨z, hz⟩
    exact hc.mpr (hp.mp ⟨Over.homMk z hz⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationOpenCharts
