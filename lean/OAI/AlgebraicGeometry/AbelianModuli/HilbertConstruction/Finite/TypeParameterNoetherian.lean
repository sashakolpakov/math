import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Type Parameter Noetherian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian

noncomputable section

/-! Finite-type parameter schemes and the self-products of their base changes over noetherian schemes are noetherian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem finiteType_noetherian_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

theorem finiteTypeParameter_pullback_selfProduct_noetherian {S U : Scheme.{u}}
    (M : Over S) [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    (k : U ⟶ S) [IsNoetherian U] :
    IsNoetherian (pullback ((Over.pullback k).obj M).hom ((Over.pullback k).obj M).hom) := by
  have ht : LocallyOfFiniteType (pullback.snd M.hom k) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback M.hom k) inferInstance
  have hq : QuasiCompact (pullback.snd M.hom k) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback M.hom k) inferInstance
  have hN : IsNoetherian (pullback M.hom k) := finiteType_noetherian_source (pullback.snd M.hom k)
  let p := pullback.snd M.hom k
  have ht' : LocallyOfFiniteType (pullback.snd p p) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback p p) ht
  have hq' : QuasiCompact (pullback.snd p p) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback p p) hq
  exact @finiteType_noetherian_source _ _ (pullback.snd p p) ht' hq' hN

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
