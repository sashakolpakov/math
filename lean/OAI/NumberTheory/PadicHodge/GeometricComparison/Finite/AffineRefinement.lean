import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover

/-! # Affine Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineRefinement.FiniteAffineRefinement

noncomputable section

/-! Every open covering family of a quasi-compact scheme admits an actual finite affine refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

structure Refinement where
  Index : Type u
  finite : Fintype Index
  opens : Index → X.Opens
  index : Index → ι
  affine : ∀ i, IsAffineOpen (opens i)
  cover : iSup opens = ⊤
  le : ∀ i, opens i ≤ U (index i)

attribute [instance] Refinement.finite

def ofCompact [CompactSpace X] (hU : iSup U = ⊤) : Refinement U := by
  classical
  have hi (x : X) : ∃ i, x ∈ U i := by
    have hx : x ∈ iSup U := hU.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    simpa only [Opens.mem_iSup] using hx
  choose j hj using hi
  choose W hW hxW hsub using fun x => exists_isAffineOpen_mem_and_subset (hj x)
  let H := CompactSpace.elim_nhds_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen.mem_nhds (hxW x))
  let t := H.choose
  have ht := H.choose_spec
  refine {
    Index := t
    finite := inferInstance
    opens := fun x => W x.1
    index := fun x => j x.1
    affine := fun x => hW x.1
    le := fun x => hsub x.1
    cover := ?_ }
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ (⋃ y ∈ t, (W y : Set X)) := ht.symm ▸ Set.mem_univ x
  rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
  rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
  exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hxy⟩

def overAffine (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
    [QuasiCompact X.hom] {ι : Type} (U : ι → X.left.Opens) (hU : iSup U = ⊤) : Refinement U := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ofCompact U hU

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineRefinement.FiniteAffineRefinement
