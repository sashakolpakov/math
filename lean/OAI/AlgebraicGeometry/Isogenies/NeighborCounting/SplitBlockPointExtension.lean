import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockGroups

/-! # Split Block Point Extension -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension.Group

/-! A finite evaluation field already contains every point of its
split group scheme. Extension to any further field induces the actual
point-group isomorphism, with the original labels and pullback map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration.Lifts

def schemePointPrecompHom {S : Scheme.{0}} {T U H : Over S} [GrpObj H]
    (a : T ⟶ U) : (U ⟶ H) →* (T ⟶ H) where
  toFun x := a ≫ x
  map_one' := MonObj.comp_one a
  map_mul' x y := MonObj.comp_mul a x y

variable {k : Type} [Field k] {X : Over (Spec (.of k))} [GrpObj X]
  (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField k X) (K : Type) [Field K] (φ : d.carrier →+* K)

abbrev pointExtensionHom :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ X) →*
      (d.extendedParameterBase K φ ⟶ X) :=
  schemePointPrecompHom (d.parameterExtensionMap K φ)

theorem pointExtensionHom_label (a : ULift (Fin d.count)) :
    pointExtensionHom d K φ (d.parameterPointEquiv a) = d.extendedParameterPointEquiv K φ a :=
  (d.extendedParameterPointEquiv_natural K φ a).symm

theorem pointExtensionHom_bijective : Function.Bijective (pointExtensionHom d K φ) := by
  constructor
  · intro a b hab
    obtain ⟨i, rfl⟩ := d.parameterPointEquiv.surjective a
    obtain ⟨j, rfl⟩ := d.parameterPointEquiv.surjective b
    rw [pointExtensionHom_label, pointExtensionHom_label] at hab
    exact congrArg d.parameterPointEquiv ((d.extendedParameterPointEquiv K φ).injective hab)
  · intro a
    obtain ⟨i, rfl⟩ := (d.extendedParameterPointEquiv K φ).surjective a
    exact ⟨d.parameterPointEquiv i, pointExtensionHom_label d K φ i⟩

def pointExtensionGroupEquiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ X) ≃*
      (d.extendedParameterBase K φ ⟶ X) :=
  MulEquiv.ofBijective (pointExtensionHom d K φ) (pointExtensionHom_bijective d K φ)

theorem pointExtensionGroupEquiv_apply
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ X) :
    pointExtensionGroupEquiv d K φ a = d.parameterExtensionMap K φ ≫ a := rfl

end AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension.Group

namespace AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension

/-! The actual extension map on a split torsion group restricts to
an isomorphism on each original projector block. No separate splitting
field or new block labels are introduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockGroups.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension.Group

variable {k : Type} [Field k] {X : Over (Spec (.of k))} [GrpObj X] [IsCommMonObj X]
  (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField k X) (K : Type) [Field K] (φ : d.carrier →+* K)
  (p : X ⟶ X) [IsMonHom p]

abbrev fixedPointExtensionHom :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p) →*
      (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p) :=
  Group.schemePointPrecompHom (d.parameterExtensionMap K φ)

theorem fixedPointExtensionHom_bijective : Function.Bijective (fixedPointExtensionHom d K φ p) := by
  let δ := d.parameterExtensionMap K φ
  let e := Group.pointExtensionGroupEquiv d K φ
  constructor
  · intro a b hab
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p)).mp
    apply e.injective
    change δ ≫ (a ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p) = δ ≫ (b ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p)
    change δ ≫ a = δ ≫ b at hab
    rw [← Category.assoc, ← Category.assoc, hab]
  · intro a
    let t := e.symm (a ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p)
    have ht : δ ≫ t = a ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p := e.apply_symm_apply _
    have hfixed : t ≫ p = t := by
      apply e.injective
      change δ ≫ (t ≫ p) = δ ≫ t
      rw [← Category.assoc, ht, Category.assoc, AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion_fixed]
    refine ⟨AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointLift p t hfixed, ?_⟩
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p)).mp
    change (δ ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointLift p t hfixed) ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p = a ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion p
    rw [Category.assoc, AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointLift_inclusion]
    exact ht

def fixedPointExtensionGroupEquiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p) ≃*
      (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p) :=
  MulEquiv.ofBijective (fixedPointExtensionHom d K φ p) (fixedPointExtensionHom_bijective d K φ p)

theorem fixedPointExtensionGroupEquiv_apply
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier))) ⟶ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme p) :
    fixedPointExtensionGroupEquiv d K φ p a = d.parameterExtensionMap K φ ≫ a := rfl

end AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension

end

end OAI
