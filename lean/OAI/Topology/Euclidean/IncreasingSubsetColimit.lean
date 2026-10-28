import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order

/-! # Increasing Subset Colimit -/

namespace OAI.Topology.Euclidean.IncreasingSubsetColimit.Globalization

noncomputable section

/-!
# Colimits over an increasing union of indexing subsets

The construction uses the actual restrictions of a diagram on a preorder.
The universal property is proved by placing any two indices in a common
stage. It applies to compact-support diagrams once compact containment in
one member of an increasing open cover has been established.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v u

variable {P : Type} [Preorder P] {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{0, 0} C]

set_option backward.isDefEq.respectTransparency false

/-- Restrict a diagram to the indicated subset of its actual preorder of indices. -/
def subsetDiagram (F : P ⥤ C) (T : Set P) : T ⥤ C :=
  (Subtype.mono_coe (· ∈ T)).functor ⋙ F

/-- The identity on underlying indices for an inclusion of subsets. -/
def subsetInclusion {S T : Set P} (h : S ⊆ T) : S ⥤ T where
  obj p := ⟨p.val, h p.property⟩
  map f := homOfLE (leOfHom f)

/-- Enlarge the allowed subset of indices in the actual colimit. -/
def subsetColimitMap (F : P ⥤ C) {S T : Set P} (h : S ⊆ T) :
    colimit (subsetDiagram F S) ⟶ colimit (subsetDiagram F T) :=
  colimit.pre (subsetDiagram F T) (subsetInclusion h)

@[reassoc (attr := simp)]
theorem subsetColimitMap_ι (F : P ⥤ C) {S T : Set P} (h : S ⊆ T) (p : S) :
    colimit.ι (subsetDiagram F S) p ≫ subsetColimitMap F h =
      colimit.ι (subsetDiagram F T) ⟨p.val, h p.property⟩ :=
  colimit.ι_pre (subsetDiagram F T) (subsetInclusion h) p

@[simp]
theorem subsetColimitMap_id (F : P ⥤ C) (T : Set P) :
    subsetColimitMap F (Set.Subset.refl T) = 𝟙 _ := by
  apply colimit.hom_ext
  intro p
  simp

@[reassoc (attr := simp)]
theorem subsetColimitMap_comp (F : P ⥤ C) {S T V : Set P}
    (h : S ⊆ T) (h' : T ⊆ V) :
    subsetColimitMap F h ≫ subsetColimitMap F h' = subsetColimitMap F (h.trans h') := by
  apply colimit.hom_ext
  intro p
  simp

/-- The map from a restricted colimit to the full diagram's colimit. -/
def subsetColimitToAmbient (F : P ⥤ C) (T : Set P) :
    colimit (subsetDiagram F T) ⟶ colimit F :=
  colimit.pre F (Subtype.mono_coe (· ∈ T)).functor

@[reassoc (attr := simp)]
theorem subsetColimitToAmbient_ι (F : P ⥤ C) (T : Set P) (p : T) :
    colimit.ι (subsetDiagram F T) p ≫ subsetColimitToAmbient F T =
      colimit.ι F p.val :=
  colimit.ι_pre F (Subtype.mono_coe (· ∈ T)).functor p

@[reassoc (attr := simp)]
theorem subsetColimitMap_toAmbient (F : P ⥤ C) {S T : Set P} (h : S ⊆ T) :
    subsetColimitMap F h ≫ subsetColimitToAmbient F T = subsetColimitToAmbient F S := by
  apply colimit.hom_ext
  intro p
  simp

/-- First form the colimit over each member of an increasing sequence of subsets. -/
def increasingSubsetDiagram (F : P ⥤ C) (S : ℕ → Set P) (hS : Monotone S) : ℕ ⥤ C where
  obj n := colimit (subsetDiagram F (S n))
  map f := subsetColimitMap F (hS (leOfHom f))
  map_id n := subsetColimitMap_id F (S n)
  map_comp f g := (subsetColimitMap_comp F (hS (leOfHom f)) (hS (leOfHom g))).symm

/-- Its actual cocone into the full colimit. -/
def increasingSubsetCocone (F : P ⥤ C) (S : ℕ → Set P) (hS : Monotone S) :
    Cocone (increasingSubsetDiagram F S hS) where
  pt := colimit F
  ι :=
    { app n := subsetColimitToAmbient F (S n)
      naturality _ _ f := by
        change subsetColimitMap F _ ≫ subsetColimitToAmbient F _ = _ ≫ 𝟙 _
        rw [subsetColimitMap_toAmbient, Category.comp_id] }

variable {F : P ⥤ C} {S : ℕ → Set P} {hS : Monotone S}

/-- A cocone on the increasing sequence assigns a map to each represented index. -/
def increasingSubsetStageMap (s : Cocone (increasingSubsetDiagram F S hS))
    (n : ℕ) (p : S n) : F.obj p.val ⟶ s.pt :=
  colimit.ι (subsetDiagram F (S n)) p ≫ s.ι.app n

theorem increasingSubsetStageMap_le (s : Cocone (increasingSubsetDiagram F S hS))
    {i j : ℕ} (hij : i ≤ j) (p : S i) :
    increasingSubsetStageMap s j ⟨p.val, hS hij p.property⟩ =
      increasingSubsetStageMap s i p := by
  unfold increasingSubsetStageMap
  rw [← subsetColimitMap_ι_assoc F (hS hij) p]
  congr 1
  exact s.w (homOfLE hij)

/-- Different containing stages give the same map. -/
theorem increasingSubsetStageMap_eq (s : Cocone (increasingSubsetDiagram F S hS))
    {i j : ℕ} {p : P} (hi : p ∈ S i) (hj : p ∈ S j) :
    increasingSubsetStageMap s i ⟨p, hi⟩ = increasingSubsetStageMap s j ⟨p, hj⟩ := by
  rw [← increasingSubsetStageMap_le s (Nat.le_max_left i j) ⟨p, hi⟩,
    ← increasingSubsetStageMap_le s (Nat.le_max_right i j) ⟨p, hj⟩]

/-- The stage maps respect every actual order morphism once both indices are represented. -/
@[reassoc]
theorem increasingSubsetStageMap_naturality
    (s : Cocone (increasingSubsetDiagram F S hS)) {i j : ℕ} {p q : P}
    (hi : p ∈ S i) (hj : q ∈ S j) (f : p ⟶ q) :
    F.map f ≫ increasingSubsetStageMap s j ⟨q, hj⟩ =
      increasingSubsetStageMap s i ⟨p, hi⟩ := by
  rw [← increasingSubsetStageMap_le s (Nat.le_max_right i j) ⟨q, hj⟩,
    ← increasingSubsetStageMap_le s (Nat.le_max_left i j) ⟨p, hi⟩]
  let p' : S (max i j) := ⟨p, hS (Nat.le_max_left i j) hi⟩
  let q' : S (max i j) := ⟨q, hS (Nat.le_max_right i j) hj⟩
  change (subsetDiagram F (S (max i j))).map (homOfLE (leOfHom f) : p' ⟶ q') ≫
    colimit.ι _ q' ≫ s.ι.app _ = colimit.ι _ p' ≫ s.ι.app _
  rw [colimit.w_assoc]

variable (F S hS)

/-- Maps from a cocone on the sequence descend to every index in the covered diagram. -/
def increasingSubsetDescCocone (hcover : ∀ p, ∃ n, p ∈ S n)
    (s : Cocone (increasingSubsetDiagram F S hS)) : Cocone F where
  pt := s.pt
  ι :=
    { app p := increasingSubsetStageMap s (Classical.choose (hcover p))
        ⟨p, Classical.choose_spec (hcover p)⟩
      naturality p q f := by
        change F.map f ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact increasingSubsetStageMap_naturality s _ _ f }

theorem increasingSubsetDescCocone_app (hcover : ∀ p, ∃ n, p ∈ S n)
    (s : Cocone (increasingSubsetDiagram F S hS)) (n : ℕ) (p : S n) :
    (increasingSubsetDescCocone F S hS hcover s).ι.app p.val =
      increasingSubsetStageMap s n p :=
  increasingSubsetStageMap_eq s _ p.property

/-- An increasing union containing every index computes the original colimit. -/
def increasingSubsetIsColimit (hcover : ∀ p, ∃ n, p ∈ S n) :
    IsColimit (increasingSubsetCocone F S hS) where
  desc s := colimit.desc F (increasingSubsetDescCocone F S hS hcover s)
  fac s n := by
    apply colimit.hom_ext
    intro p
    change colimit.ι (subsetDiagram F (S n)) p ≫
      subsetColimitToAmbient F (S n) ≫ _ = _
    rw [subsetColimitToAmbient_ι_assoc, colimit.ι_desc,
      increasingSubsetDescCocone_app]
    rfl
  uniq s m hm := by
    apply colimit.hom_ext (F := F)
    intro p
    obtain ⟨n, hp⟩ := hcover p
    rw [colimit.ι_desc, increasingSubsetDescCocone_app F S hS hcover s n ⟨p, hp⟩]
    change colimit.ι F p ≫ m = colimit.ι (subsetDiagram F (S n)) ⟨p, hp⟩ ≫ s.ι.app n
    rw [← subsetColimitToAmbient_ι F (S n) ⟨p, hp⟩, Category.assoc]
    exact congrArg (fun f => colimit.ι (subsetDiagram F (S n)) ⟨p, hp⟩ ≫ f) (hm n)

/-- The resulting canonical comparison of the iterated colimit with the full one. -/
def increasingSubsetColimitIso (hcover : ∀ p, ∃ n, p ∈ S n) :
    colimit (increasingSubsetDiagram F S hS) ≅ colimit F :=
  (colimit.isColimit _).coconePointUniqueUpToIso (increasingSubsetIsColimit F S hS hcover)

@[reassoc (attr := simp)]
theorem increasingSubsetColimitIso_ι (hcover : ∀ p, ∃ n, p ∈ S n) (n : ℕ) :
    colimit.ι (increasingSubsetDiagram F S hS) n ≫
        (increasingSubsetColimitIso F S hS hcover).hom =
      subsetColimitToAmbient F (S n) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

/-- The same sequence has a cocone into any containing subset of the original indices. -/
def increasingSubsetTargetCocone (T : Set P) (hST : ∀ n, S n ⊆ T) :
    Cocone (increasingSubsetDiagram F S hS) where
  pt := colimit (subsetDiagram F T)
  ι :=
    { app n := subsetColimitMap F (hST n)
      naturality _ _ f := by
        change subsetColimitMap F _ ≫ subsetColimitMap F _ = _ ≫ 𝟙 _
        rw [subsetColimitMap_comp, Category.comp_id] }

/-- Descend to the actual restriction to a covered target subset. -/
def increasingSubsetTargetDescCocone (T : Set P) (hcover : ∀ p ∈ T, ∃ n, p ∈ S n)
    (s : Cocone (increasingSubsetDiagram F S hS)) : Cocone (subsetDiagram F T) where
  pt := s.pt
  ι :=
    { app p := increasingSubsetStageMap s (Classical.choose (hcover p.val p.property))
        ⟨p.val, Classical.choose_spec (hcover p.val p.property)⟩
      naturality p q f := by
        change F.map (homOfLE (leOfHom f)) ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact increasingSubsetStageMap_naturality s _ _ (homOfLE (leOfHom f)) }

theorem increasingSubsetTargetDescCocone_app (T : Set P)
    (hcover : ∀ p ∈ T, ∃ n, p ∈ S n) (s : Cocone (increasingSubsetDiagram F S hS))
    (n : ℕ) (p : S n) (hp : p.val ∈ T) :
    (increasingSubsetTargetDescCocone F S hS T hcover s).ι.app ⟨p.val, hp⟩ =
      increasingSubsetStageMap s n p :=
  increasingSubsetStageMap_eq s _ p.property

/-- An increasing sequence covering a target subset computes its restricted colimit. -/
def increasingSubsetTargetIsColimit (T : Set P) (hST : ∀ n, S n ⊆ T)
    (hcover : ∀ p ∈ T, ∃ n, p ∈ S n) :
    IsColimit (increasingSubsetTargetCocone F S hS T hST) where
  desc s := colimit.desc _ (increasingSubsetTargetDescCocone F S hS T hcover s)
  fac s n := by
    apply colimit.hom_ext
    intro p
    change colimit.ι (subsetDiagram F (S n)) p ≫ subsetColimitMap F (hST n) ≫ _ = _
    rw [subsetColimitMap_ι_assoc, colimit.ι_desc,
      increasingSubsetTargetDescCocone_app]
    rfl
  uniq s m hm := by
    apply colimit.hom_ext (F := subsetDiagram F T)
    intro p
    obtain ⟨n, hp⟩ := hcover p.val p.property
    rw [colimit.ι_desc,
      increasingSubsetTargetDescCocone_app F S hS T hcover s n ⟨p.val, hp⟩ p.property]
    change colimit.ι (subsetDiagram F T) p ≫ m =
      colimit.ι (subsetDiagram F (S n)) ⟨p.val, hp⟩ ≫ s.ι.app n
    rw [← subsetColimitMap_ι F (hST n) ⟨p.val, hp⟩, Category.assoc]
    exact congrArg (fun f => colimit.ι (subsetDiagram F (S n)) ⟨p.val, hp⟩ ≫ f) (hm n)

/-- Canonical comparison with the colimit on a covered target subset. -/
def increasingSubsetTargetColimitIso (T : Set P) (hST : ∀ n, S n ⊆ T)
    (hcover : ∀ p ∈ T, ∃ n, p ∈ S n) :
    colimit (increasingSubsetDiagram F S hS) ≅ colimit (subsetDiagram F T) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (increasingSubsetTargetIsColimit F S hS T hST hcover)

@[reassoc (attr := simp)]
theorem increasingSubsetTargetColimitIso_ι (T : Set P) (hST : ∀ n, S n ⊆ T)
    (hcover : ∀ p ∈ T, ∃ n, p ∈ S n) (n : ℕ) :
    colimit.ι (increasingSubsetDiagram F S hS) n ≫
        (increasingSubsetTargetColimitIso F S hS T hST hcover).hom =
      subsetColimitMap F (hST n) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

end

end OAI.Topology.Euclidean.IncreasingSubsetColimit.Globalization
