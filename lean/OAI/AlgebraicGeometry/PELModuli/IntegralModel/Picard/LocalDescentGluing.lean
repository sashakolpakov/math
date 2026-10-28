import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicOpenSquare
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulPullbackUnit
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization

/-! # Local Descent Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LocalDescentGluing.PicardLocalDescentGluing

noncomputable section

/-! Local descents through the actual open pullback comparisons glue to
one global morphism. All comparisons are the native geometric ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicOpenSquare.PicardIntrinsicOpenSquare
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulPullbackUnit.PicardFaithfulPullbackUnit OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization.PicardOpenFactorization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
variable {M N : Y.Modules} (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
variable (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)

include hN in
theorem existsUnique_hom_of_local_descent
    {ι : Type*} (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (c : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hc : ∀ i,
      (Scheme.Modules.pullback (f ∣_ U i)).map (c i) ≫
          (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).inv.app N =
        (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).inv.app M ≫
          (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U i).ι).map q) :
    ∃! a : M ⟶ N, (Scheme.Modules.pullback f).map a = q := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : Mono (adj.unit.app N) := FaithfulPullbackUnit.PicardFaithfulPullbackUnit.unit_line_mono f hN
  let b := adj.homEquiv _ _ q
  let d (i) : (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N :=
    ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M).homCongr
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app N) (c i)
  have hd (i) : d i ≫ (Scheme.Modules.pullback (U i).ι).map (adj.unit.app N) =
      (Scheme.Modules.pullback (U i).ι).map b := by
    have := IntrinsicOpenSquare.PicardIntrinsicOpenSquare.canonical_rightMate_isIso f (U i)
    have he := Isogenies.NeighborCounting.AdjointSquareFactorization.factorization_of_square adj
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U i))
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).symm q (c i) (hc i)
    exact Isogenies.NeighborCounting.AdjointSquareFactorization.transport_factorization (Scheme.Modules.restrictFunctorIsoPullback (U i).ι)
      (c i) (adj.unit.app N) b he
  obtain ⟨a, ha, hu⟩ := OpenFactorization.PicardOpenFactorization.existsUnique_open_factorization M (adj.unit.app N) b U hU d hd
  have he (a : M ⟶ N) : adj.homEquiv _ _ ((Scheme.Modules.pullback f).map a) = a ≫ adj.unit.app N := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  refine ⟨a, (adj.homEquiv _ _).injective ((he a).trans ha), ?_⟩
  intro a' ha'
  apply hu
  exact (he a').symm.trans (congrArg (adj.homEquiv _ _) ha')

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LocalDescentGluing.PicardLocalDescentGluing
