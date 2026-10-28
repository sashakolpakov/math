import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf

/-! # Compact Support Excision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision

noncomputable section

/-!
# Excision around compact supports

An open neighborhood of a compact subset in a Hausdorff space computes the
same actual relative singular homology with that support. The comparison is
the inclusion of pairs and commutes with shrinking supports and restriction
to points. No excision or orientation data is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable (X : TopCat.{0}) (U K : Set X)

/-- A compact subset lying inside a subspace is compact in that subspace. -/
theorem compactSupport_preimage_isCompact (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K) :=
  Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)

private theorem support_complement_cover (hKU : K ⊆ U) : U ∪ Kᶜ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ K
  · exact Or.inl (hKU hx)
  · exact Or.inr hx

/-- The actual inclusion of pairs `(U, U \ K) → (X, X \ K)`. -/
def compactSupportExcisionChainMap :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) ⟶
      LocalHomology.Cycles.relativeSingularChains X Kᶜ :=
  LocalExcision.Cycles.relativeCoverInclusion X U Kᶜ

/-- The comparison is induced by inclusion on ordinary singular chains. -/
@[reassoc (attr := simp)]
theorem compactSupportExcisionChainMap_projection :
    LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) ≫
        compactSupportExcisionChainMap X U K =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X U) ≫
        LocalHomology.Cycles.relativeChainProjection X Kᶜ :=
  LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Actual excision around a compact support in an open neighborhood. -/
theorem compactSupportExcisionChainMap_quasiIso [T2Space X]
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    _root_.QuasiIso (compactSupportExcisionChainMap X U K) :=
  LocalExcision.Cycles.relativeCoverInclusion_quasiIso X U Kᶜ hU hK.isClosed.isOpen_compl
    (support_complement_cover X U K hKU)

/-- The canonical compact-support excision isomorphism on actual relative
singular homology, induced by the inclusion of pairs. -/
def compactSupportExcisionHomologyIso [T2Space X]
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) n ≅
      LocalHomology.Cycles.relativeSingularHomology X Kᶜ n :=
  LocalExcision.Cycles.relativeCoverHomologyIso X U Kᶜ hU hK.isClosed.isOpen_compl
    (support_complement_cover X U K hKU) n

@[simp]
theorem compactSupportExcisionHomologyIso_hom [T2Space X]
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ) :
    (compactSupportExcisionHomologyIso X U K hK hU hKU n).hom =
      HomologicalComplex.homologyMap (compactSupportExcisionChainMap X U K) n := rfl

/-- The inclusion of pairs commutes with decreasing the support set. This
chain-level naturality does not require compactness or openness. -/
@[reassoc]
theorem compactSupportExcisionChainMap_restriction {K L : Set X} (hKL : K ⊆ L) :
    compactSupportExcisionChainMap X U L ≫ LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL =
      LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of U)
          (show (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K ⊆ (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' L from
            Set.preimage_mono hKL) ≫
        compactSupportExcisionChainMap X U K := by
  unfold compactSupportExcisionChainMap LocalExcision.Cycles.relativeCoverInclusion LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp, LocalHomology.Cycles.relativeSingularChainsMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- Compact-support excision is natural under restrictions `K ⊆ L ⊆ U`. -/
@[reassoc]
theorem compactSupportExcisionHomologyIso_naturality [T2Space X]
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hU : IsOpen U) (hKL : K ⊆ L) (hLU : L ⊆ U) (n : ℕ) :
    (compactSupportExcisionHomologyIso X U L hL hU hLU n).hom ≫
        HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n =
      HomologicalComplex.homologyMap
          (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of U)
            (show (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K ⊆ (LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' L from
              Set.preimage_mono hKL)) n ≫
        (compactSupportExcisionHomologyIso X U K hK hU (hKL.trans hLU) n).hom := by
  rw [compactSupportExcisionHomologyIso_hom, compactSupportExcisionHomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportExcisionChainMap_restriction]

/-- Restriction to a point commutes with the actual compact-support pair map. -/
@[reassoc]
theorem compactSupportExcisionChainMap_toPoint (x : X) (hxK : x ∈ K) (hxU : x ∈ U) :
    compactSupportExcisionChainMap X U K ≫ LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X K x hxK =
      LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)
          (⟨x, hxU⟩ : U) hxK ≫
        LocalExcision.Cycles.localExcisionChainMap X U x hxU := by
  unfold compactSupportExcisionChainMap LocalExcision.Cycles.relativeCoverInclusion
    LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint LocalExcision.Cycles.localExcisionChainMap
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp, LocalHomology.Cycles.relativeSingularChainsMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- Compact-support excision and local excision give the same restriction to
the actual local homology at each point of the compact set. -/
@[reassoc]
theorem compactSupportExcisionHomologyIso_toPoint [T2Space X]
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (x : X) (hxK : x ∈ K) (n : ℕ) :
    (compactSupportExcisionHomologyIso X U K hK hU hKU n).hom ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hxK n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)
          (⟨x, hKU hxK⟩ : U) hxK n ≫
        (LocalExcision.Cycles.localExcisionHomologyIso X U x (hKU hxK) hU n).hom := by
  rw [compactSupportExcisionHomologyIso_hom, LocalExcision.Cycles.localExcisionHomologyIso_hom]
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportExcisionChainMap_toPoint]

/-- The inverse compact-support comparison is also compatible with the
inverse local comparison at each point. -/
@[reassoc]
theorem compactSupportExcisionHomologyIso_inv_toPoint [T2Space X]
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (x : X) (hxK : x ∈ K) (n : ℕ) :
    (compactSupportExcisionHomologyIso X U K hK hU hKU n).inv ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' K)
          (⟨x, hKU hxK⟩ : U) hxK n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hxK n ≫
        (LocalExcision.Cycles.localExcisionHomologyIso X U x (hKU hxK) hU n).inv := by
  apply (cancel_mono (LocalExcision.Cycles.localExcisionHomologyIso X U x (hKU hxK) hU n).hom).mp
  rw [Category.assoc, ← compactSupportExcisionHomologyIso_toPoint X U K hK hU hKU x hxK n,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision
