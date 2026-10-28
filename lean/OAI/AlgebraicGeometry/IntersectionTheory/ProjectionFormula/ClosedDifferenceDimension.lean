import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Closed Difference Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedDifferenceDimension

noncomputable section

section

/-! Every component of a closure coming from an open subscheme
has a closed witness in that open, outside any closed set not containing it. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace ClosureComponentWitness

def closedImage {X : Scheme} (U : X.Opens) (A : Closeds (U : Scheme)) : Closeds X :=
  ⟨closure (U.ι '' (A : Set (U : Scheme))), isClosed_closure⟩

theorem meets_open {X : Scheme} [NoetherianSpace X]
    (U : X.Opens) (A : Closeds (U : Scheme))
    (C : irreducibleComponents (closedImage U A)) :
    ∃ x : X, x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X (closedImage U A) C ∧ x ∈ U := by
  let S := closedImage U A
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X)
  obtain ⟨o, ho, ⟨z, hz⟩, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C.val C.property
  obtain ⟨V, hV, heV⟩ := isOpen_induced_iff.mp ho
  have hzV : z.val ∈ V := by
    change z ∈ (Subtype.val : S → X) ⁻¹' V
    rw [heV]
    exact hz
  have hzc : z.val ∈ closure (U.ι '' (A : Set (U : Scheme))) := z.property
  obtain ⟨x, hxV, hxA⟩ := mem_closure_iff.mp hzc V hV hzV
  have hxS : x ∈ S := subset_closure hxA
  have hxC : (⟨x, hxS⟩ : S) ∈ C.val := by
    apply hoC
    rw [← heV]
    exact hxV
  refine ⟨x, ⟨⟨x, hxS⟩, hxC, rfl⟩, ?_⟩
  obtain ⟨y, _, hy⟩ := hxA
  exact hy ▸ y.property

theorem closed_witness {X : Scheme} [NoetherianSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (U : X.Opens) (A : Closeds (U : Scheme)) (F : Closeds X)
    (C : irreducibleComponents (closedImage U A))
    (hC : ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X (closedImage U A) C : Set X) ⊆ F) :
    ∃ x : X, x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X (closedImage U A) C ∧
      x ∈ U ∧ x ∉ F ∧ IsClosed ({x} : Set X) := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let W := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X (closedImage U A) C
  obtain ⟨x, hxW, hxU⟩ := meets_open U A C
  have hnF : ((W : Set X) ∩ (F : Set X)ᶜ).Nonempty := by
    by_contra hn
    apply hC
    intro y hy
    by_contra hyF
    exact hn ⟨y, hy, hyF⟩
  have hn := W.isIrreducible.isPreirreducible U (F : Set X)ᶜ U.isOpen F.isClosed.isOpen_compl
    ⟨x, hxW, hxU⟩ hnF
  obtain ⟨y, ⟨hyW, hyU, hyF⟩, hyc⟩ := nonempty_inter_closedPoints hn
    (W.isClosed.isLocallyClosed.inter (U.isOpen.inter F.isClosed.isOpen_compl).isLocallyClosed)
  exact ⟨y, hyW, hyU, hyF, hyc⟩

end ClosureComponentWitness

end

/-! Removing a closed subset before taking closure discards the
components contained in it and retains the dimension bounds on the others. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

variable {S : Scheme} (I F : Closeds S)

def openComplement : S.Opens := ⟨(F : Set S)ᶜ, F.isClosed.isOpen_compl⟩

def onOpen : Closeds ((openComplement F) : Scheme) :=
  ⟨(openComplement F).ι ⁻¹' (I : Set S), I.isClosed.preimage (openComplement F).ι.continuous⟩

def away : Closeds S := ClosureComponentWitness.closedImage (openComplement F) (onOpen I F)

theorem away_coe : (away I F : Set S) = closure ((I : Set S) \ F) := by
  change closure (_ '' _) = _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

theorem subset : away I F ≤ I := by
  change (away I F : Set S) ⊆ I
  rw [away_coe]
  exact closure_minimal Set.sdiff_subset I.isClosed

theorem component_not_subset [NoetherianSpace S] (C : irreducibleComponents (away I F)) :
    ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport S (away I F) C : Set S) ⊆ F := by
  obtain ⟨x, hxC, hxU⟩ := ClosureComponentWitness.meets_open (openComplement F) (onOpen I F) C
  exact fun h => hxU (h hxC)

theorem bound [NoetherianSpace S] (f : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (k d : ℕ)
    (hI : ∀ C : IrreducibleCloseds S, (C : Set S) ⊆ I → ¬ (C : Set S) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f + k ≤ d) :
    ∀ C : IrreducibleCloseds S, (C : Set S) ⊆ away I F → Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f + k ≤ d := by
  intro C hC
  obtain ⟨D, hD⟩ := Supports.closedComponentSupport_covers S (away I F) C hC
  have hdim := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone hD
  have hb := hI (CycleClass.Thom.IntersectionGeometry.closedComponentSupport S (away I F) D)
    ((Supports.closedComponentSupport_subset S (away I F) D).trans (subset I F)) (component_not_subset I F D)
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedDifferenceDimension
