import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairCechMaps
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Over

/-! # Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.KernelPair.Construction

noncomputable section

/-! The actual kernel pair and its triple overlap remain Noetherian
for a locally finitely presented map with Noetherian source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y Z : Over S}

theorem over_pullback_fst_locallyOfFinitePresentation (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation g.left] :
    LocallyOfFinitePresentation (pullback.fst f g).left := by
  have H : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    Functor.map_isPullback (Over.forget S) (IsPullback.of_hasPullback f g)
  exact MorphismProperty.of_isPullback H.flip inferInstance

theorem over_pullback_noetherian (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsLocallyNoetherian X.left] [LocallyOfFinitePresentation g.left] :
    IsLocallyNoetherian (pullback f g).left := by
  have := over_pullback_fst_locallyOfFinitePresentation f g
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g).left

theorem kernelPair_noetherian (f : X ⟶ Y)
    [IsLocallyNoetherian X.left] [LocallyOfFinitePresentation f.left] :
    IsLocallyNoetherian (Kernel.PairCechMaps.Construction.KernelPairDescent.Relation f).left :=
  over_pullback_noetherian f f

theorem kernelPair_triple_noetherian (f : X ⟶ Y)
    [IsLocallyNoetherian X.left] [LocallyOfFinitePresentation f.left] :
    IsLocallyNoetherian (Kernel.PairCechMaps.Construction.KernelPairDescent.Triple f).left := by
  have := kernelPair_noetherian f
  have := over_pullback_fst_locallyOfFinitePresentation f f
  exact over_pullback_noetherian (pullback.snd f f) (pullback.fst f f)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.KernelPair.Construction
