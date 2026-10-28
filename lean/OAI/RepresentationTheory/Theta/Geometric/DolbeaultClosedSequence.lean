import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultSheafOneExact
import OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel

/-! # Dolbeault Closed Sequence -/

namespace OAI.RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence

noncomputable section

/-! The genuine short exact sequence from holomorphic functions to
smooth zero-forms and then to closed antiholomorphic one-forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def holomorphicDbarClosedSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  kernel (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)

def holomorphicDbarClosedMap :
    AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0 ⟶ holomorphicDbarClosedSheaf E M :=
  kernel.lift (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0)
    (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap_squared E M 0)

theorem holomorphicDbarClosedMap_ι :
    holomorphicDbarClosedMap E M ≫ kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) =
      AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0 := kernel.lift_ι _ _ _

theorem holomorphicToPureZero_closedMap :
    AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf (E := E) (M := M) ≫ holomorphicDbarClosedMap E M = 0 := by
  apply (cancel_mono (kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1))).mp
  rw [Category.assoc, holomorphicDbarClosedMap_ι, zero_comp]
  exact AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf_d

def holomorphicDbarClosedSequence : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf (holomorphicDbarClosedMap E M)
    (holomorphicToPureZero_closedMap E M)

def holomorphicDbarClosedComparison : holomorphicDbarClosedSequence E M ⟶
    AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M) where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
  comm₁₂ := by
    simp only [Category.id_comp, Category.comp_id]
    rfl
  comm₂₃ := by
    change 𝟙 _ ≫ AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0 =
      holomorphicDbarClosedMap E M ≫ kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
    rw [holomorphicDbarClosedMap_ι, Category.id_comp]

theorem holomorphicDbarClosedSequence_shortExact [FiniteDimensional ℂ E] :
    (holomorphicDbarClosedSequence E M).ShortExact := by
  let φ := holomorphicDbarClosedComparison E M
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)))
  have hex : (holomorphicDbarClosedSequence E M).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
      AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence_exact
  have hmono : Mono (holomorphicDbarClosedSequence E M).f :=
    AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf_mono
  have hepi : Epi (holomorphicDbarClosedSequence E M).g :=
    (AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultSheafOneExact.pureManifoldDolbeaultOneSequence_exact E M).epi_kernelLift
  exact { exact := hex, mono_f := hmono, epi_g := hepi }

end

end OAI.RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence
