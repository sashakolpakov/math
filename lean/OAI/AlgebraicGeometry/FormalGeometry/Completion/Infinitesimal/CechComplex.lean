import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaces

/-! # Cech Complex -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechComplex.Construction

noncomputable section

/-! The actual infinitesimal base-change comparison is an isomorphism of native Cech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem relativeStructureCechComplex_d_succ (q : ℕ) :
    (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d q (q + 1) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • RelativeCechFaces.Construction.relativeStructureCechCoface f U q k := by
  change (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
    ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U).d q (q + 1)) = _
  rw [SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d]
  simp only [SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential, Functor.map_sum, Functor.map_zsmul,
    RelativeCechFaces.Construction.relativeStructureCechCoface]

variable [X.IsSeparated] [Finite ι] (hU : ∀ i, IsAffineOpen (U i))

theorem infinitesimalCechTermIso_d_succ (n q : ℕ) :
    (CechTerms.Construction.infinitesimalCechTermIso I f U hU n q).hom ≫
        (RelativeCechZeroCycles.Construction.relativeStructureCechComplex (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
          (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i)).d q (q + 1) =
      (AdicReduction.Construction.adicReductionComplex (I ^ (n + 1)) (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)).d q (q + 1) ≫
        (CechTerms.Construction.infinitesimalCechTermIso I f U hU n (q + 1)).hom := by
  change _ = (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map
    ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d q (q + 1)) ≫ _
  rw [relativeStructureCechComplex_d_succ, relativeStructureCechComplex_d_succ]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [CechFaces.Construction.infinitesimalCechTermIso_coface]

/-- Actual reduction of the native Cech complex is the native complex on the actual infinitesimal scheme. -/
def infinitesimalCechComplexIso (n : ℕ) :
    AdicReduction.Construction.adicReductionComplex (I ^ (n + 1)) (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U) ≅
      RelativeCechZeroCycles.Construction.relativeStructureCechComplex (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) :=
  HomologicalComplex.Hom.isoOfComponents (CechTerms.Construction.infinitesimalCechTermIso I f U hU n) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    exact infinitesimalCechTermIso_d_succ I f U hU n i)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechComplex.Construction
