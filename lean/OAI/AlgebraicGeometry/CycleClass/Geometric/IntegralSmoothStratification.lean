import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratification
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

/-! # Integral Smooth Stratification -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Finite stratifications by actual integral smooth pieces

A nonempty Noetherian reduced scheme has a nonempty integral open subscheme:
choose an open subset contained in one irreducible component. Taking its
actual smooth locus over a perfect field produces an integral smooth open
piece. Noetherian induction on the closed complement gives a finite disjoint
cover by such pieces. The boundary of each piece is contained in later pieces;
its closure need not equal the entire remaining closed set.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- A smooth locally closed geometric piece whose actual carrier is integral. -/
structure IntegralSmoothStratification.IntegralSmoothGeometricPiece (f : X ⟶ Y) extends SmoothStratification.SmoothGeometricPiece f where
  integral : IsIntegral carrier

namespace IntegralSmoothStratification.IntegralSmoothGeometricPiece

variable {f : X ⟶ Y}

instance carrier_isIntegral (P : IntegralSmoothGeometricPiece f) : IsIntegral P.carrier :=
  P.integral

instance inclusion_isImmersion (P : IntegralSmoothGeometricPiece f) :
    IsImmersion P.inclusion := P.immersion

instance structureMap_isSmooth (P : IntegralSmoothGeometricPiece f) :
    Smooth (P.inclusion ≫ f) := P.smooth

/-- The actual locally closed image in the ambient scheme. -/
def support (P : IntegralSmoothGeometricPiece f) : Set X := Set.range P.inclusion

theorem isLocallyClosed_support (P : IntegralSmoothGeometricPiece f) :
    IsLocallyClosed P.support := P.inclusion.isLocallyClosed_range

theorem support_nonempty (P : IntegralSmoothGeometricPiece f) : P.support.Nonempty :=
  Set.range_nonempty _

theorem isIrreducible_support (P : IntegralSmoothGeometricPiece f) :
    IsIrreducible P.support := by
  simpa only [IntegralSmoothGeometricPiece.support, Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ P.carrier).image P.inclusion
      P.inclusion.continuous.continuousOn

end IntegralSmoothStratification.IntegralSmoothGeometricPiece

/-- Every nonempty Noetherian reduced scheme contains a nonempty integral open. -/
theorem IntegralSmoothStratification.exists_integral_open [NoetherianSpace X] [Nonempty X] [IsReduced X] :
    ∃ U : X.Opens, Nonempty U ∧ IsIntegral U.toScheme := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨o, ho, hne, hsubset⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  let U : X.Opens := ⟨o, ho⟩
  have hU : IsIrreducible (U : Set X) :=
    ⟨hne, isIrreducible_irreducibleComponent.isPreirreducible.open_subset ho hsubset⟩
  let : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hU
  exact ⟨U, inferInstance, isIntegral_of_irreducibleSpace_of_isReduced U.toScheme⟩

variable {K : Type u} [Field K] [PerfectField K]

/-- The canonical function-field dimension of an integral smooth piece. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.inclusion ≫ f)

/-- The actual smooth locus of an integral open in a reduced closed subset,
included into that reduced closed scheme. -/
def IntegralSmoothStratification.integralOpenSmoothImmersion (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] :
    SmoothStratum.smoothStratum (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ⟶ ReducedClosed.reducedClosedScheme Z :=
  SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ≫ U.ι

instance IntegralSmoothStratification.integralOpenSmoothImmersion_isOpenImmersion (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    IsOpenImmersion (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) := by
  unfold IntegralSmoothStratification.integralOpenSmoothImmersion
  infer_instance

/-- The integral smooth open piece, viewed as an actual locally closed piece
of the original ambient scheme. -/
def IntegralSmoothStratification.integralOpenSmoothPiece (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] : IntegralSmoothStratification.IntegralSmoothGeometricPiece f where
  carrier := SmoothStratum.smoothStratum (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)
  inclusion := IntegralSmoothStratification.integralOpenSmoothImmersion Z f U ≫ ReducedClosed.reducedClosedι Z
  immersion := by infer_instance
  smooth := by
    dsimp only [IntegralSmoothStratification.integralOpenSmoothImmersion]
    rw [Category.assoc, Category.assoc]
    exact SmoothStratum.smoothStratumToBase_isSmooth (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)
  integral := inferInstance

/-- Removing this actual open image leaves a closed subset of the ambient scheme. -/
def IntegralSmoothStratification.integralOpenSmoothRemainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] : Closeds X :=
  ⟨(ReducedClosed.reducedClosedι Z) '' (Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U))ᶜ,
    (ReducedClosed.reducedClosedι Z).isClosedEmbedding.isClosedMap _
      (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U).isOpenEmbedding.isOpen_range.isClosed_compl⟩

@[simp]
theorem IntegralSmoothStratification.integralOpenSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support =
      (ReducedClosed.reducedClosedι Z) '' Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) := by
  change Set.range ((ReducedClosed.reducedClosedι Z) ∘ (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U)) = _
  exact Set.range_comp _ _

theorem IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support ∪
      (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U : Set X) = Z := by
  rw [IntegralSmoothStratification.integralOpenSmoothPiece_support]
  change (ReducedClosed.reducedClosedι Z) '' Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) ∪
    (ReducedClosed.reducedClosedι Z) '' (Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U))ᶜ = _
  rw [Set.image_union_image_compl_eq_range, ReducedClosed.range_reducedClosedι]

theorem IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    Disjoint (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support
      (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U : Set X) := by
  rw [IntegralSmoothStratification.integralOpenSmoothPiece_support]
  apply (Set.disjoint_image_iff (ReducedClosed.reducedClosedι Z).isClosedEmbedding.injective).mpr
  exact disjoint_compl_right

theorem IntegralSmoothStratification.integralOpenSmoothRemainder_lt (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    IntegralSmoothStratification.integralOpenSmoothRemainder Z f U < Z := by
  have hcover := IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder Z f U
  apply lt_of_le_not_ge
  · intro x hx
    change x ∈ (Z : Set X)
    rw [← hcover]
    exact Or.inr hx
  · intro hge
    obtain ⟨x, hx⟩ := (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support_nonempty
    have hxZ : x ∈ (Z : Set X) := hcover ▸ Or.inl hx
    exact (Set.disjoint_left.mp (IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder Z f U))
      hx (hge hxZ)

/-- Taking the smooth locus of this integral open preserves its actual
function-field dimension. -/
theorem IntegralSmoothStratification.integralOpenSmoothPiece_dimension (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).dimension =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) := by
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (((SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ≫ U.ι) ≫
      ReducedClosed.reducedClosedι Z) ≫ f) = _
  simpa only [Category.assoc, ReducedClosed.reducedClosedStructureMap] using
    Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
      (SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f))
      (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)

/-- The underlying union of a finite list of integral smooth pieces. -/
def IntegralSmoothStratification.integralSmoothPiecesSupport {f : X ⟶ Y} :
    List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Set X
  | [] => ∅
  | P :: Ps => P.support ∪ integralSmoothPiecesSupport Ps

theorem IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport {f : X ⟶ Y}
    {P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f} {Ps : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f)}
    (hP : P ∈ Ps) : P.support ⊆ IntegralSmoothStratification.integralSmoothPiecesSupport Ps := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
      rcases List.mem_cons.mp hP with h | h
      · subst P
        exact Set.subset_union_left
      · exact Set.Subset.trans (ih h) Set.subset_union_right

/-- The boundary of each piece is contained in the union of the later pieces. -/
def IntegralSmoothStratification.integralSmoothPiecesFrontier {f : X ⟶ Y} :
    List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Prop
  | [] => True
  | P :: Ps => closure P.support \ P.support ⊆ IntegralSmoothStratification.integralSmoothPiecesSupport Ps ∧
      integralSmoothPiecesFrontier Ps

/-- A finite disjoint cover by actual integral smooth locally closed schemes,
ordered so that each piece's boundary is contained in the remaining pieces. -/
structure IntegralSmoothStratification.IntegralSmoothGeometricStratification (f : X ⟶ Y) (S : Set X) where
  pieces : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
  disjoint : pieces.Pairwise (fun P Q => Disjoint P.support Q.support)
  cover : IntegralSmoothStratification.integralSmoothPiecesSupport pieces = S
  frontier : IntegralSmoothStratification.integralSmoothPiecesFrontier pieces

namespace IntegralSmoothStratification.IntegralSmoothGeometricStratification

variable {f : X ⟶ Y}

/-- The empty closed subset has its empty stratification. -/
def empty : IntegralSmoothGeometricStratification f ∅ where
  pieces := []
  disjoint := List.Pairwise.nil
  cover := rfl
  frontier := True.intro

/-- Adjoin an integral smooth piece to a stratified closed remainder. -/
def cons {S T : Set X} (P : IntegralSmoothGeometricPiece f)
    (Q : IntegralSmoothGeometricStratification f T) (hd : Disjoint P.support T)
    (hc : P.support ∪ T = S) (hcl : closure P.support ⊆ S) :
    IntegralSmoothGeometricStratification f S where
  pieces := P :: Q.pieces
  disjoint := List.pairwise_cons.mpr ⟨fun R hR => hd.mono_right (by
    rw [← Q.cover]
    exact support_subset_integralSmoothPiecesSupport hR), Q.disjoint⟩
  cover := by
    change P.support ∪ IntegralSmoothStratification.integralSmoothPiecesSupport Q.pieces = S
    rw [Q.cover]
    exact hc
  frontier := ⟨by
    rw [Q.cover]
    intro x hx
    have hxS := hcl hx.1
    rw [← hc] at hxS
    exact hxS.resolve_left hx.2, Q.frontier⟩

/-- Every chosen piece lies in the prescribed underlying set. -/
theorem piece_support_subset {S : Set X} (Q : IntegralSmoothGeometricStratification f S)
    {P : IntegralSmoothGeometricPiece f} (hP : P ∈ Q.pieces) : P.support ⊆ S := by
  rw [← Q.cover]
  exact support_subset_integralSmoothPiecesSupport hP

end IntegralSmoothStratification.IntegralSmoothGeometricStratification

/-- Every closed subset of a Noetherian finite-type scheme over a perfect field
admits a finite disjoint stratification by actual integral smooth schemes. -/
theorem IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed [NoetherianSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (Z : Closeds X) :
    Nonempty (IntegralSmoothStratification.IntegralSmoothGeometricStratification f (Z : Set X)) := by
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  by_cases hZ : Z = ⊥
  · subst Z
    exact ⟨IntegralSmoothStratification.IntegralSmoothGeometricStratification.empty⟩
  · let : NoetherianSpace (ReducedClosed.reducedClosedScheme Z) :=
      (ReducedClosed.reducedClosedι Z).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    let : Nonempty (ReducedClosed.reducedClosedScheme Z) :=
      ReducedClosed.reducedClosedScheme_nonempty Z (Closeds.coe_nonempty.mpr hZ)
    obtain ⟨U, _, hU⟩ := IntegralSmoothStratification.exists_integral_open (X := ReducedClosed.reducedClosedScheme Z)
    let : IsIntegral U.toScheme := hU
    obtain ⟨Q⟩ := ih (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U)
      (IntegralSmoothStratification.integralOpenSmoothRemainder_lt Z f U)
    have hc := IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder Z f U
    refine ⟨IntegralSmoothStratification.IntegralSmoothGeometricStratification.cons (IntegralSmoothStratification.integralOpenSmoothPiece Z f U) Q
      (IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder Z f U) hc ?_⟩
    apply closure_minimal _ Z.isClosed
    intro x hx
    rw [← hc]
    exact Or.inl hx

/-- The finite-type hypotheses imply the required topological Noetherianity. -/
theorem IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (IntegralSmoothStratification.IntegralSmoothGeometricStratification f Set.univ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  exact IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed f ⊤

/-- Choose only after proving existence of the actual finite stratification. -/
def IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IntegralSmoothStratification.IntegralSmoothGeometricStratification f Set.univ :=
  Classical.choice (IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_of_finiteType f)

/-- Genuine dimension-graded cycle supports, including singular supports, admit
a finite stratification by integral smooth locally closed schemes. -/
def DimensionCycles.DimensionCycleSupport.integralSmoothGeometricStratification
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : DimensionCycles.DimensionCycleSupport V p) :
    IntegralSmoothStratification.IntegralSmoothGeometricStratification Z.structureMap Set.univ :=
  IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType Z.structureMap

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
