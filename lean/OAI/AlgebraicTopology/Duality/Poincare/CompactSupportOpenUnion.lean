import OAI.Topology.Euclidean.IncreasingSubsetColimit
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen

/-! # Compact Support Open Union -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpenUnion

noncomputable section

section

/-!
# Compact-support cohomology of increasing open unions

Every compact support in an increasing union of open subsets is already
contained in one member. We first apply this fact to the actual diagram of
ambient relative cohomology. The checked fixed-support excision comparison
then transports that colimit to the compact-support cohomology of the actual
open subspaces. The final comparison uses the already defined open-extension
maps, as verified on every stage.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.Topology.Euclidean.IncreasingSubsetColimit.Globalization

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Monotone open subsets give monotone subsets of the actual compact-support index. -/
theorem increasingOpenCompacts_monotone (U : ℕ → Opens X) (hU : Monotone U) :
    Monotone (fun i => (U i).compactsInside) := by
  intro i j hij K hK x hx
  exact hU hij (hK hx)

/-- A compact support in an increasing open union is contained in a single member. -/
theorem compactSupportIndex_in_increasingOpen (U : ℕ → Opens X) (hU : Monotone U)
    (K : Compacts X) (hK : K ∈ (⨆ i, U i).compactsInside) :
    ∃ i, K ∈ (U i).compactsInside := by
  change (K : Set X) ⊆ (⨆ i, U i : Opens X) at hK
  apply K.isCompact.elim_directed_cover (fun i => (U i : Set X)) (fun i => (U i).isOpen)
  · simpa only [Opens.coe_iSup] using hK
  · intro i j
    exact ⟨max i j, hU (Nat.le_max_left i j), hU (Nat.le_max_right i j)⟩

/-- Group the actual ambient relative cohomology stages by an increasing sequence of opens. -/
def compactSupportIncreasingInsideDiagram (M : ModuleCat.{0} R)
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) : ℕ ⥤ ModuleCat.{0} R :=
  Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetDiagram (CompactSupportCohomology.compactSupportCohomologyDiagram M X n)
    (fun i => (U i).compactsInside) (increasingOpenCompacts_monotone U hU)

/-- The colimit over the sequence contains exactly the compact supports of its union. -/
def compactSupportIncreasingInsideUnionIso (M : ModuleCat.{0} R)
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    colimit (compactSupportIncreasingInsideDiagram M U hU n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M (⨆ i, U i) n :=
  Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetTargetColimitIso (CompactSupportCohomology.compactSupportCohomologyDiagram M X n)
    (fun i => (U i).compactsInside) (increasingOpenCompacts_monotone U hU)
    (⨆ i, U i).compactsInside
    (fun i _ hK _ hx => (le_iSup U i) (hK hx))
    (compactSupportIndex_in_increasingOpen U hU)

@[reassoc (attr := simp)]
theorem compactSupportIncreasingInsideUnionIso_ι (M : ModuleCat.{0} R)
    (U : ℕ → Opens X) (hU : Monotone U) (n i : ℕ) :
    colimit.ι (compactSupportIncreasingInsideDiagram M U hU n) i ≫
        (compactSupportIncreasingInsideUnionIso M U hU n).hom =
      CompactSupportInsideMaps.compactSupportInsideMap M (le_iSup U i) n :=
  Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetTargetColimitIso_ι (CompactSupportCohomology.compactSupportCohomologyDiagram M X n)
    (fun j => (U j).compactsInside) (increasingOpenCompacts_monotone U hU)
    (⨆ j, U j).compactsInside (fun j _ hK _ hx => (le_iSup U j) (hK hx))
    (compactSupportIndex_in_increasingOpen U hU) i

/-- If the increasing opens cover the whole space, the grouped stages compute actual `Hc(X)`. -/
def compactSupportIncreasingInsideAmbientIso (M : ModuleCat.{0} R)
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    colimit (compactSupportIncreasingInsideDiagram M U hU n) ≅
      CompactSupportCohomology.compactSupportedCohomology M X n :=
  Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetColimitIso (CompactSupportCohomology.compactSupportCohomologyDiagram M X n)
    (fun i => (U i).compactsInside) (increasingOpenCompacts_monotone U hU)
    (fun K => compactSupportIndex_in_increasingOpen U hU K
      (fun x _ => Opens.mem_iSup.mpr (hcover x))) ≪≫
    CompactSupportColimit.compactSupportCohomologyColimitIso M X n

@[reassoc (attr := simp)]
theorem compactSupportIncreasingInsideAmbientIso_ι (M : ModuleCat.{0} R)
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n i : ℕ) :
    colimit.ι (compactSupportIncreasingInsideDiagram M U hU n) i ≫
        (compactSupportIncreasingInsideAmbientIso M U hU hcover n).hom =
      CompactSupportInsideMaps.compactSupportInsideToAmbient M (U i) n := by
  change colimit.ι (Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetDiagram _ _ _) i ≫
    (Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetColimitIso _ _ _ _).hom ≫
      (CompactSupportColimit.compactSupportCohomologyColimitIso M X n).hom = _
  rw [Topology.Euclidean.IncreasingSubsetColimit.Globalization.increasingSubsetColimitIso_ι_assoc]
  rfl

variable [T2Space X]

/-- The actual compact-support cohomology groups of the increasing open subspaces,
with their already constructed extension maps. -/
def compactSupportIncreasingOpenDiagram (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    ℕ ⥤ ModuleCat.{0} ℚ :=
  hU.functor ⋙ CompactSupportOpen.compactSupportOpenCohomologyFunctor X n

/-- The actual fixed-support excision comparisons identify the two sequences naturally. -/
def compactSupportIncreasingOpenDiagramIso (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    compactSupportIncreasingInsideDiagram (ModuleCat.of ℚ ℚ) U hU n ≅
      compactSupportIncreasingOpenDiagram U hU n :=
  NatIso.ofComponents (fun i => CompactSupportOpen.compactSupportOpenIndexIso (U i) n)
    (fun {_i _j} f => (CompactSupportOpen.compactSupportOpenMap_index (hU (leOfHom f)) n).symm)

/-- Compact-support cohomology of an increasing open union is the colimit of the
actual compact-support cohomology groups of its members. -/
def compactSupportIncreasingOpenUnionIso (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    colimit (compactSupportIncreasingOpenDiagram U hU n) ≅
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (⨆ i, U i : Opens X)) n :=
  (colim : (ℕ ⥤ ModuleCat.{0} ℚ) ⥤ ModuleCat.{0} ℚ).mapIso
      (compactSupportIncreasingOpenDiagramIso U hU n).symm ≪≫
    compactSupportIncreasingInsideUnionIso (ModuleCat.of ℚ ℚ) U hU n ≪≫
      CompactSupportOpen.compactSupportOpenIndexIso (⨆ i, U i) n

/-- The comparison is characterized by the genuine open-extension maps into the union. -/
@[reassoc (attr := simp)]
theorem compactSupportIncreasingOpenUnionIso_ι
    (U : ℕ → Opens X) (hU : Monotone U) (n i : ℕ) :
    colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
        (compactSupportIncreasingOpenUnionIso U hU n).hom =
      CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n := by
  change colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
    colimMap (compactSupportIncreasingOpenDiagramIso U hU n).inv ≫
      (compactSupportIncreasingInsideUnionIso (ModuleCat.of ℚ ℚ) U hU n).hom ≫
        (CompactSupportOpen.compactSupportOpenIndexIso (⨆ i, U i) n).hom = _
  rw [ι_colimMap_assoc, compactSupportIncreasingInsideUnionIso_ι_assoc]
  rfl

/-- The actual open-extension cocone into the increasing union. -/
def compactSupportIncreasingOpenUnionCocone
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    Cocone (compactSupportIncreasingOpenDiagram U hU n) where
  pt := CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (⨆ i, U i : Opens X)) n
  ι :=
    { app i := CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n
      naturality _i _j f := by
        change CompactSupportOpen.compactSupportOpenMap (hU (leOfHom f)) n ≫
          CompactSupportOpen.compactSupportOpenMap (le_iSup U _j) n =
            CompactSupportOpen.compactSupportOpenMap (le_iSup U _i) n ≫ 𝟙 _
        rw [CompactSupportOpen.compactSupportOpenMap_comp, Category.comp_id] }

/-- The genuine open-extension cocone has the colimit universal property. -/
def compactSupportIncreasingOpenUnionIsColimit
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    IsColimit (compactSupportIncreasingOpenUnionCocone U hU n) :=
  (colimit.isColimit _).ofIsoColimit
    (Cocone.ext (compactSupportIncreasingOpenUnionIso U hU n)
      (compactSupportIncreasingOpenUnionIso_ι U hU n))

/-- The union comparison preserves the class of every actual compact support. -/
@[reassoc (attr := simp)]
theorem compactSupportIncreasingOpenUnionIso_stage
    (U : ℕ → Opens X) (hU : Monotone U) (n i : ℕ) (K : (U i).compactsInside) :
    CompactSupportOpen.compactSupportOpenStageClass (U i) K n ≫
        colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
          (compactSupportIncreasingOpenUnionIso U hU n).hom =
      CompactSupportOpen.compactSupportOpenStageClass (⨆ j, U j)
        ((CompactSupportInsideMaps.compactsInsideMap (le_iSup U i)).obj K) n := by
  rw [compactSupportIncreasingOpenUnionIso_ι, CompactSupportOpen.compactSupportOpenStageClass_map]

/-- For a cover of the ambient space, the sequence computes actual ambient compact-support
cohomology through the original open-extension maps. -/
def compactSupportIncreasingOpenAmbientIso (U : ℕ → Opens X) (hU : Monotone U)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    colimit (compactSupportIncreasingOpenDiagram U hU n) ≅
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n :=
  (colim : (ℕ ⥤ ModuleCat.{0} ℚ) ⥤ ModuleCat.{0} ℚ).mapIso
      (compactSupportIncreasingOpenDiagramIso U hU n).symm ≪≫
    compactSupportIncreasingInsideAmbientIso (ModuleCat.of ℚ ℚ) U hU hcover n

@[reassoc (attr := simp)]
theorem compactSupportIncreasingOpenAmbientIso_ι (U : ℕ → Opens X) (hU : Monotone U)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n i : ℕ) :
    colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
        (compactSupportIncreasingOpenAmbientIso U hU hcover n).hom =
      CompactSupportExcision.compactSupportOpenExtension (U i) n := by
  change colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
    colimMap (compactSupportIncreasingOpenDiagramIso U hU n).inv ≫
      (compactSupportIncreasingInsideAmbientIso (ModuleCat.of ℚ ℚ) U hU hcover n).hom = _
  rw [ι_colimMap_assoc, compactSupportIncreasingInsideAmbientIso_ι]
  exact CompactSupportOpen.compactSupportOpenIndexIso_inv_toAmbient (U i) n

/-- The existing ambient open extensions form the colimit cocone for an increasing cover. -/
def compactSupportIncreasingOpenAmbientCocone
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) :
    Cocone (compactSupportIncreasingOpenDiagram U hU n) where
  pt := CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n
  ι :=
    { app i := CompactSupportExcision.compactSupportOpenExtension (U i) n
      naturality _i _j f := by
        change CompactSupportOpen.compactSupportOpenMap (hU (leOfHom f)) n ≫
          CompactSupportExcision.compactSupportOpenExtension (U _j) n =
            CompactSupportExcision.compactSupportOpenExtension (U _i) n ≫ 𝟙 _
        rw [CompactSupportOpen.compactSupportOpenMap_extension, Category.comp_id] }

/-- The ambient cocone has the colimit universal property for an increasing cover. -/
def compactSupportIncreasingOpenAmbientIsColimit
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    IsColimit (compactSupportIncreasingOpenAmbientCocone U hU n) :=
  (colimit.isColimit _).ofIsoColimit
    (Cocone.ext (compactSupportIncreasingOpenAmbientIso U hU hcover n)
      (compactSupportIncreasingOpenAmbientIso_ι U hU hcover n))

/-- The ambient comparison sends each represented compact class to its original `Hc(X)` class. -/
@[reassoc (attr := simp)]
theorem compactSupportIncreasingOpenAmbientIso_stage
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n i : ℕ) (K : (U i).compactsInside) :
    CompactSupportOpen.compactSupportOpenStageClass (U i) K n ≫
        colimit.ι (compactSupportIncreasingOpenDiagram U hU n) i ≫
          (compactSupportIncreasingOpenAmbientIso U hU hcover n).hom =
      CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K.val n := by
  rw [compactSupportIncreasingOpenAmbientIso_ι, CompactSupportOpen.compactSupportOpenStageClass_extension]

end

/-!
# Classes in compact-support cohomology of increasing open unions

The actual open-extension colimit gives representatives at finite open
stages. Equality and vanishing are detected at a common later stage.
These statements apply both to the union as an open subspace and to an
ambient space covered by the sequence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [T2Space X]

/-- Every class of the open union comes from an actual member of the increasing sequence. -/
theorem compactSupportIncreasingUnion_exists_stage
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (⨆ i, U i : Opens X)) n) :
    ∃ (i : ℕ) (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n),
      CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n a = c :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{0} ℚ))
      (compactSupportIncreasingOpenUnionIsColimit U hU n)) c

/-- A representative of a class in the union can be chosen beyond any prescribed stage. -/
theorem compactSupportIncreasingUnion_exists_stage_ge
    (U : ℕ → Opens X) (hU : Monotone U) (n N : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (⨆ i, U i : Opens X)) n) :
    ∃ (i : ℕ) (_ : N ≤ i)
      (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n),
      CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n a = c := by
  obtain ⟨i, a, ha⟩ := compactSupportIncreasingUnion_exists_stage U hU n c
  refine ⟨max N i, Nat.le_max_left N i,
    CompactSupportOpen.compactSupportOpenMap (hU (Nat.le_max_right N i)) n a, ?_⟩
  change (CompactSupportOpen.compactSupportOpenMap (hU (Nat.le_max_right N i)) n ≫
    CompactSupportOpen.compactSupportOpenMap (le_iSup U (max N i)) n) a = c
  rw [CompactSupportOpen.compactSupportOpenMap_comp]
  exact ha

/-- Two classes agree in the union exactly when they agree after extension to a common stage. -/
theorem compactSupportIncreasingUnion_eq_iff
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) {i j : ℕ}
    (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U j)) n) :
    CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n a = CompactSupportOpen.compactSupportOpenMap (le_iSup U j) n b ↔
      ∃ (k : ℕ) (hi : i ≤ k) (hj : j ≤ k),
        CompactSupportOpen.compactSupportOpenMap (hU hi) n a = CompactSupportOpen.compactSupportOpenMap (hU hj) n b := by
  have heq := Types.FilteredColimit.isColimit_eq_iff
    (compactSupportIncreasingOpenDiagram U hU n ⋙ forget (ModuleCat.{0} ℚ))
    (isColimitOfPreserves (forget (ModuleCat.{0} ℚ))
      (compactSupportIncreasingOpenUnionIsColimit U hU n)) (xi := a) (xj := b)
  constructor
  · intro h
    obtain ⟨k, f, g, hab⟩ := heq.mp h
    exact ⟨k, leOfHom f, leOfHom g, hab⟩
  · rintro ⟨k, hi, hj, hab⟩
    exact heq.mpr ⟨k, homOfLE hi, homOfLE hj, hab⟩

/-- A class vanishes in the union exactly when it vanishes after extension to a later stage. -/
theorem compactSupportIncreasingUnion_eq_zero_iff
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ) {i : ℕ}
    (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n) :
    CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n a = 0 ↔
      ∃ (k : ℕ) (hi : i ≤ k), CompactSupportOpen.compactSupportOpenMap (hU hi) n a = 0 := by
  constructor
  · intro h
    have h' : CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n a =
        CompactSupportOpen.compactSupportOpenMap (le_iSup U i) n 0 := by simpa using h
    obtain ⟨k, hi, _hi', ha⟩ := (compactSupportIncreasingUnion_eq_iff U hU n a 0).mp h'
    exact ⟨k, hi, by simpa using ha⟩
  · rintro ⟨k, hi, ha⟩
    have h' := (compactSupportIncreasingUnion_eq_iff U hU n a 0).mpr
      ⟨k, hi, hi, by simpa using ha⟩
    simpa using h'

/-- Every ambient class is represented on a member of an increasing open cover. -/
theorem compactSupportIncreasingAmbient_exists_stage
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) :
    ∃ (i : ℕ) (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n),
      CompactSupportExcision.compactSupportOpenExtension (U i) n a = c :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{0} ℚ))
      (compactSupportIncreasingOpenAmbientIsColimit U hU hcover n)) c

/-- The representing member of an increasing open cover can be chosen arbitrarily late. -/
theorem compactSupportIncreasingAmbient_exists_stage_ge
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n N : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) :
    ∃ (i : ℕ) (_ : N ≤ i)
      (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n),
      CompactSupportExcision.compactSupportOpenExtension (U i) n a = c := by
  obtain ⟨i, a, ha⟩ := compactSupportIncreasingAmbient_exists_stage U hU hcover n c
  refine ⟨max N i, Nat.le_max_left N i,
    CompactSupportOpen.compactSupportOpenMap (hU (Nat.le_max_right N i)) n a, ?_⟩
  change (CompactSupportOpen.compactSupportOpenMap (hU (Nat.le_max_right N i)) n ≫
    CompactSupportExcision.compactSupportOpenExtension (U (max N i)) n) a = c
  rw [CompactSupportOpen.compactSupportOpenMap_extension]
  exact ha

/-- Equality in ambient compact-support cohomology is detected inside one later open set. -/
theorem compactSupportIncreasingAmbient_eq_iff
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) {i j : ℕ}
    (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U j)) n) :
    CompactSupportExcision.compactSupportOpenExtension (U i) n a = CompactSupportExcision.compactSupportOpenExtension (U j) n b ↔
      ∃ (k : ℕ) (hi : i ≤ k) (hj : j ≤ k),
        CompactSupportOpen.compactSupportOpenMap (hU hi) n a = CompactSupportOpen.compactSupportOpenMap (hU hj) n b := by
  have heq := Types.FilteredColimit.isColimit_eq_iff
    (compactSupportIncreasingOpenDiagram U hU n ⋙ forget (ModuleCat.{0} ℚ))
    (isColimitOfPreserves (forget (ModuleCat.{0} ℚ))
      (compactSupportIncreasingOpenAmbientIsColimit U hU hcover n)) (xi := a) (xj := b)
  constructor
  · intro h
    obtain ⟨k, f, g, hab⟩ := heq.mp h
    exact ⟨k, leOfHom f, leOfHom g, hab⟩
  · rintro ⟨k, hi, hj, hab⟩
    exact heq.mpr ⟨k, homOfLE hi, homOfLE hj, hab⟩

/-- Vanishing in ambient compact-support cohomology is detected inside a later open set. -/
theorem compactSupportIncreasingAmbient_eq_zero_iff
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) {i : ℕ}
    (a : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U i)) n) :
    CompactSupportExcision.compactSupportOpenExtension (U i) n a = 0 ↔
      ∃ (k : ℕ) (hi : i ≤ k), CompactSupportOpen.compactSupportOpenMap (hU hi) n a = 0 := by
  constructor
  · intro h
    have h' : CompactSupportExcision.compactSupportOpenExtension (U i) n a =
        CompactSupportExcision.compactSupportOpenExtension (U i) n 0 := by simpa using h
    obtain ⟨k, hi, _hi', ha⟩ :=
      (compactSupportIncreasingAmbient_eq_iff U hU hcover n a 0).mp h'
    exact ⟨k, hi, by simpa using ha⟩
  · rintro ⟨k, hi, ha⟩
    have h' := (compactSupportIncreasingAmbient_eq_iff U hU hcover n a 0).mpr
      ⟨k, hi, hi, by simpa using ha⟩
    simpa using h'

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpenUnion
