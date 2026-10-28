import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Components -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Integrality of the actual complex PEL components follows from the
supplied smooth, proper, geometrically connected component geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

theorem Components.smooth_proper_connected_integral (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] :
    IsIntegral X.left := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  let : ConnectedSpace X.left := GeometricallyConnected.connectedSpace_of_subsingleton X.hom
  let : IsReduced X.left := AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced X.hom
  let x : X.left := Classical.choice inferInstance
  let C : irreducibleComponents X.left :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hC : IsClopen (C : Set X.left) :=
    ⟨isClosed_of_mem_irreducibleComponents _ C.property,
      AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains (AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain X.hom)
        (finite_irreducibleComponents_of_isNoetherian (X := X.left)) C.property⟩
  have hfull : (C : Set X.left) = Set.univ := hC.eq_univ ⟨x, mem_irreducibleComponent⟩
  let : IrreducibleSpace X.left := (irreducibleSpace_def X.left).mpr (by
    change IsIrreducible Set.univ
    rw [← hfull]
    exact C.property.1)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.component_smooth_proper_connected (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    Smooth (D.componentComplex j).hom ∧ IsProper (D.componentComplex j).hom ∧
      GeometricallyConnected (D.componentComplex j).hom := by
  let : Smooth (D.pel.components.S j).hom := (hg.componentGeometry j).1
  let : IsProper (D.pel.components.S j).hom := (hg.componentGeometry j).2.1
  let : GeometricallyConnected (D.pel.components.S j).hom := (hg.componentGeometry j).2.2.2
  dsimp [Data.ActiveHeckeThetaData.componentComplex, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentGeneric]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem Data.ActiveHeckeThetaData.component_integral (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    IsIntegral (D.componentComplex j).left := by
  obtain ⟨hs, hp, hc⟩ := D.component_smooth_proper_connected hg j
  let := hs
  let := hp
  let := hc
  exact Components.smooth_proper_connected_integral (D.componentComplex j)

end

end OAI.RepresentationTheory.Theta.Geometric
