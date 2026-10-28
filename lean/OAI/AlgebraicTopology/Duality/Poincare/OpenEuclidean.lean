import OAI.Topology.Euclidean.CountableBootstrap
import OAI.Topology.Euclidean.BoxHomeomorph
import OAI.AlgebraicTopology.Duality.Poincare.EuclideanChart
import OAI.AlgebraicTopology.Duality.Poincare.Empty
import OAI.AlgebraicTopology.Duality.Poincare.OpenUnion
import OAI.AlgebraicTopology.Duality.Poincare.MayerVietoris

/-! # Open Euclidean -/

namespace OAI.AlgebraicTopology.Duality.Poincare.OpenEuclidean

noncomputable section

/-!
# Canonical Poincare duality on spaces homeomorphic to Euclidean open sets

The topological coordinate map is used to pull back a countable basis of
rational boxes. Every basis member has the actual Euclidean homeomorphism type.
Its canonical cap product is the one supplied by its inherited complex charts;
no compatibility of the coordinate homeomorphism with those charts is required.
-/

open Set _root_.TopologicalSpace _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section PulledBackBoxes

variable {ι : Type} [Finite ι] {M : Type} [TopologicalSpace M]

/-- The countable collection of rational boxes contained in an actual open set. -/
abbrev OpenEuclideanBoxIndex (W : Opens (ι → ℝ)) :=
  {B : OAI.Topology.Euclidean.BoxBasis.Globalization.RationalBox ι // B.carrier ⊆ (W : Set (ι → ℝ))}

/-- A rational box, pulled back through a homeomorphism onto a Euclidean open set. -/
def openEuclideanBox (W : Opens (ι → ℝ)) (e : M ≃ₜ W)
    (B : OpenEuclideanBoxIndex W) : Opens M :=
  ⟨(fun x => (e x).val) ⁻¹' B.val.carrier,
    B.val.isOpen_carrier.preimage (continuous_subtype_val.comp e.continuous)⟩

@[simp]
theorem mem_openEuclideanBox (W : Opens (ι → ℝ)) (e : M ≃ₜ W)
    (B : OpenEuclideanBoxIndex W) (x : M) :
    x ∈ openEuclideanBox W e B ↔ (e x).val ∈ B.val.carrier := Iff.rfl

/-- Each pulled-back box has a genuine homeomorphism to its real coordinate space. -/
def openEuclideanBoxHomeomorph (W : Opens (ι → ℝ)) (e : M ≃ₜ W)
    (B : OpenEuclideanBoxIndex W) : openEuclideanBox W e B ≃ₜ (ι → ℝ) := by
  have hf : Topology.IsEmbedding (fun x : M => (e x).val) :=
    Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  have hB : B.val.carrier ⊆ Set.range (fun x : M => (e x).val) := by
    intro y hy
    refine ⟨e.symm ⟨y, B.property hy⟩, ?_⟩
    simp only [e.apply_symm_apply]
  exact (hf.homeomorphOfSubsetRange hB).trans B.val.homeomorphEuclidean

/-- The pulled-back boxes form a countable topological basis on the original space. -/
theorem isTopologicalBasis_openEuclideanBox (W : Opens (ι → ℝ)) (e : M ≃ₜ W) :
    IsTopologicalBasis (Set.range fun B : OpenEuclideanBoxIndex W =>
      (openEuclideanBox W e B : Set M)) := by
  let f : M → (ι → ℝ) := fun x => (e x).val
  have hf : Topology.IsOpenEmbedding f :=
    W.isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨B, rfl⟩
    exact (openEuclideanBox W e B).isOpen
  · intro x S hx hS
    obtain ⟨B, hxB, hBS⟩ := OAI.Topology.Euclidean.BoxBasis.Globalization.RationalBox.exists_mem_subset
      (hf.isOpenMap S hS) (Set.mem_image_of_mem f hx)
    have hBW : B.carrier ⊆ (W : Set (ι → ℝ)) := by
      intro y hy
      obtain ⟨z, _hz, rfl⟩ := hBS hy
      exact (e z).property
    refine ⟨(openEuclideanBox W e ⟨B, hBW⟩ : Set M),
      ⟨⟨B, hBW⟩, rfl⟩, hxB, ?_⟩
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hBS hz
    exact (hf.injective hwz) ▸ hw

/-- Intersections of pulled-back basis boxes are basis boxes or are empty. -/
theorem openEuclideanBox_inter_eq_or_empty (W : Opens (ι → ℝ)) (e : M ≃ₜ W)
    (B C : OpenEuclideanBoxIndex W) :
    (∃ D : OpenEuclideanBoxIndex W,
      (openEuclideanBox W e B : Set M) ∩ openEuclideanBox W e C =
        openEuclideanBox W e D) ∨
      (openEuclideanBox W e B : Set M) ∩ openEuclideanBox W e C = ∅ := by
  rcases OAI.Topology.Euclidean.BoxBasis.Globalization.RationalBox.inter_eq_carrier_or_empty B.val C.val with ⟨D, hD⟩ | hE
  · have hDW : D.carrier ⊆ (W : Set (ι → ℝ)) := by
      rw [← hD]
      exact Set.inter_subset_left.trans B.property
    left
    refine ⟨⟨D, hDW⟩, ?_⟩
    change (fun x : M => (e x).val) ⁻¹' B.val.carrier ∩
        (fun x : M => (e x).val) ⁻¹' C.val.carrier =
      (fun x : M => (e x).val) ⁻¹' D.carrier
    rw [← Set.preimage_inter, hD]
  · right
    change (fun x : M => (e x).val) ⁻¹' B.val.carrier ∩
        (fun x : M => (e x).val) ⁻¹' C.val.carrier = ∅
    rw [← Set.preimage_inter, hE, Set.preimage_empty]

end PulledBackBoxes

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Each pulled-back rational box satisfies actual canonical cap duality,
using its inherited complex structure and its proved Euclidean topology. -/
theorem openEuclideanBox_hasCanonicalPoincareDuality
    (W : Opens (Fin (2 * d) → ℝ)) (e : M ≃ₜ W) (B : OpenEuclideanBoxIndex W) :
    Property.HasCanonicalPoincareDuality d (openEuclideanBox W e B) :=
  EuclideanChart.euclideanChart_hasCanonicalPoincareDuality d
    ((openEuclideanBoxHomeomorph W e B).trans
      (OAI.Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm.toHomeomorph)

/-- Canonical cap duality holds for an actual complex manifold homeomorphic
to an arbitrary open subset of its real coordinate space. The proof glues the
proved box cases using the actual Mayer--Vietoris and increasing-union results. -/
theorem realOpenEuclideanChart_hasCanonicalPoincareDuality
    (W : Opens (Fin (2 * d) → ℝ)) (e : M ≃ₜ W) :
    Property.HasCanonicalPoincareDuality d M := by
  let P : Set M → Prop := fun S => ∀ hS : IsOpen S,
    Property.HasCanonicalPoincareDuality d (⟨S, hS⟩ : Opens M)
  have hPempty : P ∅ := by
    intro _h
    let : IsEmpty ↥(⊥ : Opens M) := ⟨fun x => x.property⟩
    exact Empty.hasCanonicalPoincareDuality_of_isEmpty d ↥(⊥ : Opens M)
  have hPbase : ∀ B : OpenEuclideanBoxIndex W,
      P (openEuclideanBox W e B : Set M) := by
    intro B _hB
    exact openEuclideanBox_hasCanonicalPoincareDuality d W e B
  have hPglue : ∀ A B : Set M, IsOpen A → IsOpen B →
      P A → P B → P (A ∩ B) → P (A ∪ B) := by
    intro A B hA hB hPA hPB hPAB _hAB
    exact Property.HasCanonicalPoincareDuality.sup d ⟨A, hA⟩ ⟨B, hB⟩ (hPA hA) (hPB hB) (hPAB (hA.inter hB))
  have hPlimit : ∀ a : ℕ → Set M, Monotone a → (∀ n, IsOpen (a n)) →
      (∀ n, P (a n)) → P (⋃ n, a n) := by
    intro a ha hoa hPa _ho
    have h := Property.HasCanonicalPoincareDuality.iSup d
      (fun n => ⟨a n, hoa n⟩) ha (fun n => hPa n (hoa n))
    have heq : (⨆ n, (⟨a n, hoa n⟩ : Opens M)) = ⟨⋃ n, a n, _ho⟩ :=
      Opens.iSup_mk a hoa
    exact heq ▸ h
  have hPtop : P Set.univ := OAI.Topology.Euclidean.CountableBootstrap.Globalization.property_of_countable_basis
    (fun B : OpenEuclideanBoxIndex W => (openEuclideanBox W e B : Set M))
    (isTopologicalBasis_openEuclideanBox W e)
    (openEuclideanBox_inter_eq_or_empty W e)
    P hPempty hPbase hPglue hPlimit Set.univ isOpen_univ
  exact Property.HasCanonicalPoincareDuality.of_increasingOpenCover d
    (fun _ => ⊤) monotone_const (fun _ => ⟨0, Set.mem_univ _⟩)
    (fun _ => hPtop isOpen_univ)

/-- Any actual complex manifold homeomorphic to a complex-coordinate open
set satisfies canonical Poincare duality, including higher-degree vanishing.
The homeomorphism is not required to respect the complex charts. -/
theorem openEuclideanChart_hasCanonicalPoincareDuality
    (U : Opens (Fin d → ℂ)) (e : M ≃ₜ U) : Property.HasCanonicalPoincareDuality d M :=
  realOpenEuclideanChart_hasCanonicalPoincareDuality d
    (OAI.Topology.Euclidean.OpenCoordinateTransport.Globalization.complexOpenInRealCoordinates d U)
    (e.trans (OAI.Topology.Euclidean.OpenCoordinateTransport.Globalization.complexOpenRealDiffeomorph d 1 U).toHomeomorph)

/-- In particular, every genuine complex-coordinate open subset has the
canonical cap isomorphisms and compact-support vanishing above its dimension. -/
theorem complexOpen_hasCanonicalPoincareDuality (U : Opens (Fin d → ℂ)) :
    Property.HasCanonicalPoincareDuality d U :=
  openEuclideanChart_hasCanonicalPoincareDuality d U (Homeomorph.refl U)

end

end OAI.AlgebraicTopology.Duality.Poincare.OpenEuclidean
