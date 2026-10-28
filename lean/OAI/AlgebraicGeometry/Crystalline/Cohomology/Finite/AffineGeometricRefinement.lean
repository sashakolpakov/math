import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperAffineCover

/-! # Affine Geometric Refinement -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement

noncomputable section

/-! Every open covering family of a quasi-compact scheme admits an actual finite affine refinement. -/

namespace FiniteAffineRefinement

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

def overAffine (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
    [QuasiCompact X.hom] {ι : Type u} (U : ι → X.left.Opens) (hU : iSup U = ⊤) : Refinement U := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ofCompact U hU

end FiniteAffineRefinement

/-! A quasi-compact source has an actual finite affine cover refining both a chosen source cover and the inverse image of a chosen target cover. -/

namespace FiniteAffineMapRefinement

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → X.Opens)

def intersections : ι × κ → X.Opens := fun i => V i.2 ⊓ f ⁻¹ᵁ U i.1

theorem cover (hU : iSup U = ⊤) (hV : iSup V = ⊤) : iSup (intersections f U V) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hy : f x ∈ iSup U := hU.symm ▸ (show f x ∈ (⊤ : Y.Opens) from trivial)
  have hx : x ∈ iSup V := hV.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨(i, j), hj, hi⟩

def ofCompact [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤) :
    FiniteAffineRefinement.Refinement (intersections f U V) :=
  FiniteAffineRefinement.ofCompact (intersections f U V) (FiniteAffineMapRefinement.cover f U V hU hV)

theorem le_source [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (i : (ofCompact f U V hU hV).Index) :
    (ofCompact f U V hU hV).opens i ≤ f ⁻¹ᵁ U ((ofCompact f U V hU hV).index i).1 :=
  ((ofCompact f U V hU hV).le i).trans inf_le_right

theorem le_target [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (i : (ofCompact f U V hU hV).Index) :
    (ofCompact f U V hU hV).opens i ≤ V ((ofCompact f U V hU hV).index i).2 :=
  ((ofCompact f U V hU hV).le i).trans inf_le_left

end FiniteAffineMapRefinement

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.AffineGeometricRefinement
