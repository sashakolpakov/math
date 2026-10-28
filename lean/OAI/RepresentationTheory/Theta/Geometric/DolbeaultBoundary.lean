import OAI.RepresentationTheory.Theta.Geometric.PureZeroFormSheaf
import OAI.RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence

/-! # Dolbeault Boundary -/

namespace OAI.RepresentationTheory.Theta.Geometric.DolbeaultBoundary

noncomputable section

section

/-! Closed Dolbeault one-forms represent every actual holomorphic H1
class, and their ambiguity consists exactly of derivatives of smooth functions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteDimensional ℂ E]

def holomorphicDbarGlobalMap :
    (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0).obj.obj (op (⊤ : Opens M)) →+
      (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)) :=
  ((DolbeaultClosedSequence.holomorphicDbarClosedMap E M).hom.app (op ⊤)).hom

def holomorphicDbarBoundary :
    (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)) →+
      CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 :=
  ((DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M).extClass.postcomp _
    (rfl : 0 + 1 = 1)).comp
      (CategoryTheory.Sheaf.H.equiv₀ (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M) isTerminalTop).symm.toAddMonoidHom

theorem holomorphicDbarBoundary_globalMap
    (s : (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0).obj.obj (op (⊤ : Opens M))) :
    holomorphicDbarBoundary E M (holomorphicDbarGlobalMap E M s) = 0 := by
  let S := DolbeaultClosedSequence.holomorphicDbarClosedSequence E M
  change ((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm
    (S.g.hom.app (op (⊤ : Opens M)) s)).comp
      (DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M).extClass (rfl : 0 + 1 = 1) = 0
  rw [← CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  change (((CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm s).comp
    (Ext.mk₀ S.g) (add_zero 0)).comp
      (DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M).extClass (rfl : 0 + 1 = 1) = 0
  rw [Ext.comp_assoc_of_second_deg_zero,
    (DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M).comp_extClass, Ext.comp_zero]

theorem exists_globalMap_of_dbarBoundary_zero
    (z : (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)))
    (hz : holomorphicDbarBoundary E M z = 0) :
    ∃ s : (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.abelianAntiOpenManifoldFormSheaf E M 0).obj.obj (op (⊤ : Opens M)),
      holomorphicDbarGlobalMap E M s = z := by
  let S := DolbeaultClosedSequence.holomorphicDbarClosedSequence E M
  let hS := DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M
  let e := CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ _ hS (e.symm z) (rfl : 0 + 1 = 1) hz
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop b, ?_⟩
  change S.g.hom.app (op ⊤) (CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop b) = z
  rw [CategoryTheory.Sheaf.H.equiv₀_naturality]
  change e (CategoryTheory.Sheaf.H.map S.g 0 b) = z
  change CategoryTheory.Sheaf.H.map S.g 0 b = e.symm z at hb
  rw [hb, e.apply_symm_apply]

theorem holomorphicDbarGlobalMap_range :
    (holomorphicDbarGlobalMap E M).range = (holomorphicDbarBoundary E M).ker := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact holomorphicDbarBoundary_globalMap E M s
  · exact exists_globalMap_of_dbarBoundary_zero E M z

theorem holomorphicDbarBoundary_surjective [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] :
    Function.Surjective (holomorphicDbarBoundary E M) := by
  intro v
  let S := DolbeaultClosedSequence.holomorphicDbarClosedSequence E M
  let hS := DolbeaultClosedSequence.holomorphicDbarClosedSequence_shortExact E M
  have hz : CategoryTheory.Sheaf.H.map S.f 1 v = 0 := PureZeroFormSheaf.pureZeroFormSheaf_H1_zero E M _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ _ hS v hz (rfl : 0 + 1 = 1)
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop b, ?_⟩
  change ((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm
    (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop b)).comp hS.extClass (rfl : 0 + 1 = 1) = v
  rw [AddEquiv.symm_apply_apply]
  exact hb

end

/-! Concrete global closed (0,1)-forms represent the original sheaf H1
of holomorphic functions. Their kernel is the genuine global dbar derivative. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

abbrev ClosedDbarOneForm :=
  LinearMap.ker (AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (E := E) (⊤ : Opens M) 1)

def closedDbarSectionMap :
    (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)) →+ ClosedDbarOneForm E M where
  toFun z := ⟨(kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)).hom.app (op ⊤) z, by
    change ((kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)) ≫
      AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1).hom.app (op ⊤) z = 0
    rw [kernel.condition]
    rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ z w)

theorem closedDbarSectionMap_bijective : Function.Bijective (closedDbarSectionMap E M) := by
  constructor
  · intro z w h
    apply AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafMono_section_injective (kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)) ⊤
    exact congrArg Subtype.val h
  · intro a
    let S := ShortComplex.mk (kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1))
      (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1) (kernel.condition _)
    have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel _)
    obtain ⟨z, hz⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS
      (inferInstanceAs (Mono (kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)))) a.val a.property
    exact ⟨z, Subtype.ext hz⟩

def closedDbarSectionEquiv :
    (DolbeaultClosedSequence.holomorphicDbarClosedSheaf E M).obj.obj (op (⊤ : Opens M)) ≃+ ClosedDbarOneForm E M :=
  AddEquiv.ofBijective (closedDbarSectionMap E M) (closedDbarSectionMap_bijective E M)

def globalDbarDerivative : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0 →+ ClosedDbarOneForm E M where
  toFun s := ⟨AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD ⊤ 0 s, AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_squared ⊤ 0 s⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ s t)

theorem closedDbarSectionEquiv_globalMap [FiniteDimensional ℂ E]
    (s : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0) :
    closedDbarSectionEquiv E M (holomorphicDbarGlobalMap E M s) = globalDbarDerivative E M s := by
  apply Subtype.ext
  change (DolbeaultClosedSequence.holomorphicDbarClosedMap E M ≫ kernel.ι (AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)).hom.app
    (op ⊤) s = AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD ⊤ 0 s
  rw [DolbeaultClosedSequence.holomorphicDbarClosedMap_ι]
  rfl

variable [FiniteDimensional ℂ E]

def holomorphicDbarClass : ClosedDbarOneForm E M →+
    CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 :=
  (holomorphicDbarBoundary E M).comp (closedDbarSectionEquiv E M).symm.toAddMonoidHom

theorem holomorphicDbarClass_derivative (s : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0) :
    holomorphicDbarClass E M (globalDbarDerivative E M s) = 0 := by
  rw [← closedDbarSectionEquiv_globalMap]
  change holomorphicDbarBoundary E M ((closedDbarSectionEquiv E M).symm
    (closedDbarSectionEquiv E M (holomorphicDbarGlobalMap E M s))) = 0
  rw [AddEquiv.symm_apply_apply]
  exact holomorphicDbarBoundary_globalMap E M s

theorem exists_derivative_of_dbarClass_zero (a : ClosedDbarOneForm E M)
    (ha : holomorphicDbarClass E M a = 0) :
    ∃ s : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0, globalDbarDerivative E M s = a := by
  obtain ⟨s, hs⟩ := exists_globalMap_of_dbarBoundary_zero E M
    ((closedDbarSectionEquiv E M).symm a) ha
  refine ⟨s, ?_⟩
  rw [← closedDbarSectionEquiv_globalMap, hs, AddEquiv.apply_symm_apply]

theorem globalDbarDerivative_range :
    (globalDbarDerivative E M).range = (holomorphicDbarClass E M).ker := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact holomorphicDbarClass_derivative E M s
  · exact exists_derivative_of_dbarClass_zero E M a

theorem holomorphicDbarClass_surjective [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] :
    Function.Surjective (holomorphicDbarClass E M) := by
  intro v
  obtain ⟨z, hz⟩ := holomorphicDbarBoundary_surjective E M v
  refine ⟨closedDbarSectionEquiv E M z, ?_⟩
  change holomorphicDbarBoundary E M ((closedDbarSectionEquiv E M).symm (closedDbarSectionEquiv E M z)) = v
  rw [AddEquiv.symm_apply_apply, hz]

end

end OAI.RepresentationTheory.Theta.Geometric.DolbeaultBoundary
