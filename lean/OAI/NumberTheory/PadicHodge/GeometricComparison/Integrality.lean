import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Topology.Connected.Clopen

/-! # Integrality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality.GeometricIntegrality

noncomputable section

/-! Geometric integrality follows from smoothness, geometric connectedness, and quasi-compactness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem smooth_connected_integral {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [QuasiCompact f] [ConnectedSpace X] :
    IsIntegral X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let : IsReduced X := OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced f
  let x : X := Classical.choice inferInstance
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have hopen := OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain f)
    (finite_irreducibleComponents_of_isNoetherian (X := X)) hc
  have hclopen : IsClopen (irreducibleComponent x) :=
    ⟨isClosed_of_mem_irreducibleComponents _ hc, hopen⟩
  have heq : irreducibleComponent x = Set.univ :=
    hclopen.eq_univ ⟨x, mem_irreducibleComponent⟩
  let : PreirreducibleSpace X := ⟨by simpa only [heq] using hc.1.2⟩
  let : IrreducibleSpace X := ⟨inferInstance⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem of_smooth_geometricallyConnected {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [QuasiCompact f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact snd := MorphismProperty.of_isPullback h inferInstance
  let : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) y fst snd h
  exact smooth_connected_integral snd

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality.GeometricIntegrality
