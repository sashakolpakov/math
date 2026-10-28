import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum
import OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed

/-! # Smooth Stratification -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Finite geometric smooth stratifications

A stratum below is an actual scheme with an immersion into the ambient scheme
and a proved smooth structure morphism. A stratification is a finite list of
such strata with disjoint underlying images covering the specified set.
The construction uses Noetherian induction on closed subsets. No Whitney or
analytic regularity condition is asserted.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- A genuine smooth locally closed geometric piece over the given base. -/
structure CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece (f : X ⟶ Y) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  immersion : IsImmersion inclusion
  smooth : Smooth (inclusion ≫ f)

namespace CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece

variable {f : X ⟶ Y}

instance inclusion_isImmersion (P : SmoothGeometricPiece f) :
    IsImmersion P.inclusion := P.immersion
instance structureMap_isSmooth (P : SmoothGeometricPiece f) :
    Smooth (P.inclusion ≫ f) := P.smooth

/-- The underlying set occupied by this actual geometric piece. -/
def support (P : SmoothGeometricPiece f) : Set X := Set.range P.inclusion

/-- Each stratum has locally closed image, as required for an algebraic stratum. -/
theorem isLocallyClosed_support (P : SmoothGeometricPiece f) :
    IsLocallyClosed P.support :=
  P.inclusion.isLocallyClosed_range

end CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece

/-- The underlying union of a finite list of actual strata. -/
def CycleClass.Geometric.SmoothStratification.smoothPiecesSupport {f : X ⟶ Y} : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f) → Set X
  | [] => ∅
  | P :: Ps => P.support ∪ smoothPiecesSupport Ps

theorem CycleClass.Geometric.SmoothStratification.support_subset_smoothPiecesSupport {f : X ⟶ Y}
    {P : CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f} {Ps : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f)} (hP : P ∈ Ps) :
    P.support ⊆ CycleClass.Geometric.SmoothStratification.smoothPiecesSupport Ps := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
      rcases List.mem_cons.mp hP with h | h
      · subst P
        exact Set.subset_union_left
      · exact Set.Subset.trans (ih h) Set.subset_union_right

/-- Each stratum is dense in the remaining closed tail of the ordered list.
Its closure minus itself is therefore a union of later strata. -/
def CycleClass.Geometric.SmoothStratification.smoothPiecesFrontier {f : X ⟶ Y} : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f) → Prop
  | [] => True
  | P :: Ps => closure P.support = P.support ∪ CycleClass.Geometric.SmoothStratification.smoothPiecesSupport Ps ∧
      smoothPiecesFrontier Ps

/-- Finite smooth locally closed strata with disjoint images, the frontier
condition, and an exact cover of the specified set. -/
structure CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification (f : X ⟶ Y) (S : Set X) where
  pieces : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f)
  disjoint : pieces.Pairwise (fun P Q => Disjoint P.support Q.support)
  cover : CycleClass.Geometric.SmoothStratification.smoothPiecesSupport pieces = S
  frontier : CycleClass.Geometric.SmoothStratification.smoothPiecesFrontier pieces

namespace CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification

variable {f : X ⟶ Y}

/-- The empty finite stratification. -/
def empty : SmoothGeometricStratification f ∅ where
  pieces := []
  disjoint := List.Pairwise.nil
  cover := rfl
  frontier := True.intro

/-- Adjoin one smooth geometric stratum disjoint from the already stratified set. -/
def cons {S T : Set X} (P : SmoothGeometricPiece f)
    (Q : SmoothGeometricStratification f T) (hd : Disjoint P.support T)
    (hc : P.support ∪ T = S) (hcl : closure P.support = S) :
    SmoothGeometricStratification f S where
  pieces := P :: Q.pieces
  disjoint := List.pairwise_cons.mpr ⟨fun R hR => hd.mono_right (by
    rw [← Q.cover]
    exact support_subset_smoothPiecesSupport hR), Q.disjoint⟩
  cover := by
    change P.support ∪ SmoothStratification.smoothPiecesSupport Q.pieces = S
    rw [Q.cover]
    exact hc
  frontier := ⟨by simpa only [Q.cover, hc] using hcl, Q.frontier⟩

end CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification

variable {K : Type u} [Field K]

/-- The first stratum of a closed set is the smooth open locus of its reduced
induced scheme, included back into the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratification.closedSmoothPiece (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f where
  carrier := CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)
  inclusion := CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f) ≫ CycleClass.Geometric.ReducedClosed.reducedClosedι Z
  immersion := by infer_instance
  smooth := by
    rw [Category.assoc]
    exact CycleClass.Geometric.SmoothStratum.smoothStratumToBase_isSmooth (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)

/-- The singular remainder, as a closed subset of the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratification.closedSingularRemainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : Closeds X :=
  ⟨(CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f),
    (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.isClosedMap _
      (CycleClass.Geometric.SingularLocus.isClosed_singularLocus (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f))⟩

@[simp]
theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support =
      (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus :
        Set (CycleClass.Geometric.ReducedClosed.reducedClosedScheme Z)) := by
  change Set.range ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) ∘
    (CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f))) = _
  rw [Set.range_comp, CycleClass.Geometric.SmoothStratum.range_smoothStratumι]

/-- The smooth first stratum and singular remainder form an exact partition. -/
theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support ∪ (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) = Z := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support]
  change (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _) ∪
    (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _)ᶜ = _
  rw [Set.image_union_image_compl_eq_range, CycleClass.Geometric.ReducedClosed.range_reducedClosedι]

theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Disjoint (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support]
  change Disjoint ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) ''
    ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _))
    ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _)ᶜ)
  apply (Set.disjoint_image_iff (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.injective).mpr
  exact disjoint_compl_right

theorem CycleClass.Geometric.SmoothStratification.closedSingularRemainder_le (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f ≤ Z := by
  intro x hx
  have hmem : x ∈ (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support ∪
      (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) := Or.inr hx
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder] at hmem
  exact hmem

variable [PerfectField K]

/-- The first stratum is dense in this closed set, giving the frontier condition. -/
theorem CycleClass.Geometric.SmoothStratification.closure_closedSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : closure (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support = (Z : Set X) := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support, (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.closure_image_eq,
    (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).dense_smoothLocus_of_perfectField.closure_eq,
    Set.image_univ, CycleClass.Geometric.ReducedClosed.range_reducedClosedι]

/-- Unless the closed set is empty, generic smoothness makes the singular
remainder strictly smaller. This is the decreasing measure in Noetherian induction. -/
theorem CycleClass.Geometric.SmoothStratification.closedSingularRemainder_lt (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (hZ : Z ≠ ⊥) : CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f < Z := by
  apply lt_of_le_not_ge (CycleClass.Geometric.SmoothStratification.closedSingularRemainder_le Z f)
  intro hge
  let : Nonempty (CycleClass.Geometric.ReducedClosed.reducedClosedScheme Z) :=
    CycleClass.Geometric.ReducedClosed.reducedClosedScheme_nonempty Z (Closeds.coe_nonempty.mpr hZ)
  have hnonempty : Nonempty (CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)) :=
    (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)).nonempty
  obtain ⟨a⟩ := hnonempty
  have ha : (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).inclusion a ∈ (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support :=
    Set.mem_range_self a
  have haZ : (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).inclusion a ∈ (Z : Set X) :=
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder Z f) ▸ Or.inl ha
  exact (Set.disjoint_left.mp (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder Z f)) ha (hge haZ)

/-- Noetherian induction produces finitely many actual smooth locally closed
strata, with disjoint images and the frontier condition, for every closed subset. -/
theorem CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_closed [NoetherianSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (Z : Closeds X) :
    Nonempty (CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f (Z : Set X)) := by
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  by_cases hZ : Z = ⊥
  · subst Z
    exact ⟨CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification.empty⟩
  · obtain ⟨Q⟩ := ih (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f) (CycleClass.Geometric.SmoothStratification.closedSingularRemainder_lt Z f hZ)
    exact ⟨CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification.cons (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f) Q
      (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder Z f)
      (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder Z f) (CycleClass.Geometric.SmoothStratification.closure_closedSmoothPiece_support Z f)⟩

/-- A finite-type scheme over a perfect field admits a finite smooth geometric
stratification of its underlying space. -/
theorem CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f Set.univ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  exact CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_closed f ⊤

/-- A chosen finite stratification, extracted from the proved existence theorem. -/
def CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f Set.univ :=
  Classical.choice (CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_of_finiteType f)

/-- The construction applies in particular to the actual smooth projective
complex domains in this development. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.smoothGeometricStratification
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification P.structureMap Set.univ :=
  CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType P.structureMap

/-- Every actual integral cycle support has a finite smooth stratification. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothGeometricStratification
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) Set.univ :=
  CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

end

end OAI.AlgebraicGeometry
