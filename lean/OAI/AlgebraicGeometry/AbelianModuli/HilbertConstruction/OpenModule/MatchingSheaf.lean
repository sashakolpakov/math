import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Matching Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf

noncomputable section

/-! Effective Zariski gluing of module objects, in section coordinates.
Each local module is allowed to be presented as an ambient pushforward.
The matching equations use actual linear equivalences on common opens;
their compatible sections form a genuine sheaf of modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
universe u

structure OpenModuleTransitions {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : ι → X.Modules) where
  compare : ∀ (V : X.Opens) (i j : ι), V ≤ U i → V ≤ U j →
    Γ(M i, V) ≃ₗ[Γ(X, V)] Γ(M j, V)
  natural : ∀ (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M i, V)),
    compare W i j (h.trans hi) (h.trans hj) ((M i).presheaf.map (homOfLE h).op s) =
      (M j).presheaf.map (homOfLE h).op (compare V i j hi hj s)
  identity : ∀ (V : X.Opens) (i : ι) (hi : V ≤ U i) (s : Γ(M i, V)),
    compare V i i hi hi s = s
  composition : ∀ (V : X.Opens) (i j k : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) (s : Γ(M i, V)),
    compare V j k hj hk (compare V i j hi hj s) = compare V i k hi hk s

namespace OpenModuleTransitions
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}

theorem restriction_comp (A : X.Modules) {V W Z : X.Opens}
    (h : W ≤ V) (k : Z ≤ W) (s : Γ(A, V)) :
    A.presheaf.map (homOfLE k).op (A.presheaf.map (homOfLE h).op s) =
      A.presheaf.map (homOfLE (k.trans h)).op s :=
  (ConcreteCategory.congr_hom (A.presheaf.map_comp (homOfLE h).op (homOfLE k).op) s).symm

theorem restriction_self (A : X.Modules) (V : X.Opens) (h : V ≤ V) (s : Γ(A, V)) :
    A.presheaf.map (homOfLE h).op s = s :=
  ConcreteCategory.congr_hom (A.presheaf.map_id (.op V)) s

theorem restriction_zero (A : X.Modules) {V W : X.Opens} (h : W ≤ V) :
    A.presheaf.map (homOfLE h).op (0 : Γ(A, V)) = 0 :=
  (A.presheaf.map (homOfLE h).op).hom.map_zero

theorem restriction_add (A : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (s t : Γ(A, V)) :
    A.presheaf.map (homOfLE h).op (s + t) =
      A.presheaf.map (homOfLE h).op s + A.presheaf.map (homOfLE h).op t :=
  (A.presheaf.map (homOfLE h).op).hom.map_add s t

abbrev relativeSections (A : X.Modules) (V W : X.Opens) (h : W ≤ V) : ModuleCat Γ(X, V) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj (A.val.obj (.op W))

abbrev Tuple (U : ι → X.Opens) (M : ι → X.Modules) (V : X.Opens) :=
  (i : ι) → relativeSections (M i) V (V ⊓ U i) inf_le_left

def tupleRestriction {V W : X.Opens} (h : W ≤ V) :
    Tuple U M V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Tuple U M W where
  toFun s i := (M i).presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op (s i)
  map_add' s t := funext (fun i => map_add _ (s i) (t i))
  map_smul' r s := by
    funext i
    let a : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h (le_refl (U i))
    let si : Γ(M i, V ⊓ U i) := s i
    change (M i).presheaf.map (homOfLE a).op
        (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) si) =
      (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op
        (X.presheaf.map (homOfLE h).op r)) •
          (M i).presheaf.map (homOfLE a).op si
    exact (Scheme.Modules.map_smul (M i) (homOfLE a) _ si).trans
      (congrArg (fun z : Γ(X, W ⊓ U i) => z • (M i).presheaf.map (homOfLE a).op si)
        ((Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
          (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) r).symm))

theorem tupleRestriction_self (V : X.Opens) (s : Tuple U M V) :
    tupleRestriction (le_refl V) s = s := by
  funext i
  exact restriction_self (M i) _ _ _

theorem tupleRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : Tuple U M V) :
    tupleRestriction k (tupleRestriction h s) = tupleRestriction (k.trans h) s := by
  funext i
  exact restriction_comp (M i) _ _ _

variable (D : OpenModuleTransitions U M)

def sections (V : X.Opens) : Submodule Γ(X, V) (Tuple U M V) where
  carrier := {s | ∀ i j,
    D.compare ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right
      ((M i).presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (s i)) =
    (M j).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)}
  zero_mem' := by
    intro i j
    change D.compare _ i j _ _
      ((M i).presheaf.map _ (0 : Γ(M i, V ⊓ U i))) =
        (M j).presheaf.map _ (0 : Γ(M j, V ⊓ U j))
    rw [restriction_zero, restriction_zero, map_zero]
  add_mem' := by
    intro s t hs ht i j
    let Q := (V ⊓ U i) ⊓ U j
    let a := (M i).presheaf.map
      (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op
    let b := (M j).presheaf.map
      (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op
    let c := D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
    exact (congrArg c (a.hom.map_add (s i) (t i))).trans
      ((c.map_add (a (s i)) (a (t i))).trans
        ((congrArg₂ (fun x y : Γ(M j, Q) => x + y) (hs i j) (ht i j)).trans
          (b.hom.map_add (s j) (t j)).symm))
  smul_mem' := by
    intro r s hs i j
    let Q := (V ⊓ U i) ⊓ U j
    let si : Γ(M i, V ⊓ U i) := s i
    let sj : Γ(M j, V ⊓ U j) := s j
    have hs' : D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
        ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op si) =
      (M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op sj := hs i j
    change D.compare Q i j _ _
        ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op
          (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
            (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) si)) =
      (M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op
          (@SMul.smul Γ(X, V ⊓ U j) Γ(M j, V ⊓ U j) inferInstance
            (X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r) sj)
    let a : Q ≤ V ⊓ U i := inf_le_left
    let b : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    let ri : Γ(X, V ⊓ U i) :=
      X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r
    let rj : Γ(X, V ⊓ U j) :=
      X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r
    let c := D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
    have hr : X.presheaf.map (homOfLE a).op ri = X.presheaf.map (homOfLE b).op rj :=
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
        (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U j ≤ V from inf_le_left) b r).symm
    exact (congrArg c (Scheme.Modules.map_smul (M i) (homOfLE a) ri si)).trans
      ((c.map_smul _ _).trans
        ((congrArg₂ (fun (q : Γ(X, Q)) (x : Γ(M j, Q)) => q • x) hr hs').trans
          (Scheme.Modules.map_smul (M j) (homOfLE b) rj sj).symm))

theorem mem_sections (V : X.Opens) (s : Tuple U M V) :
    s ∈ D.sections V ↔ ∀ i j,
      D.compare ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right
        ((M i).presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (s i)) =
      (M j).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j) :=
  Iff.rfl

theorem tupleRestriction_mem {V W : X.Opens} (h : W ≤ V)
    (s : Tuple U M V) (hs : s ∈ D.sections V) : tupleRestriction h s ∈ D.sections W := by
  intro i j
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have hi : (M i).presheaf.map (homOfLE (show Z ≤ W ⊓ U i from inf_le_left)).op
      (tupleRestriction h s i) =
    (M i).presheaf.map (homOfLE a).op
      ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op (s i)) := by
    exact (restriction_comp (M i) _ _ _).trans (restriction_comp (M i) _ _ _).symm
  have hj : (M j).presheaf.map (homOfLE (show Z ≤ W ⊓ U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (tupleRestriction h s j) =
    (M j).presheaf.map (homOfLE a).op
      ((M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)) := by
    exact (restriction_comp (M j) _ _ _).trans (restriction_comp (M j) _ _ _).symm
  exact (congrArg (D.compare Z i j _ _) hi).trans
    ((D.natural Q Z a i j _ _ _).trans
      ((congrArg ((M j).presheaf.map (homOfLE a).op) (hs i j)).trans hj.symm))

def sectionRestriction {V W : X.Opens} (h : W ≤ V) :
    D.sections V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] D.sections W :=
  ((tupleRestriction h).comp (D.sections V).subtype).codRestrict (D.sections W)
    (fun s => D.tupleRestriction_mem h s.val s.property)

theorem sectionRestriction_self (V : X.Opens) (s : D.sections V) :
    D.sectionRestriction (le_refl V) s = s :=
  Subtype.ext (tupleRestriction_self V s.val)

theorem sectionRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : D.sections V) :
    D.sectionRestriction k (D.sectionRestriction h s) = D.sectionRestriction (k.trans h) s :=
  Subtype.ext (tupleRestriction_comp h k s.val)

def modulePresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (D.sections V.unop)
  map {V W} h := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, V.unop) (D.sections V.unop))
    (Y := (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
      (ModuleCat.of Γ(X, W.unop) (D.sections W.unop)))
    { __ := (D.sectionRestriction h.unop.le).toAddMonoidHom
      map_smul' := (D.sectionRestriction h.unop.le).map_smul' }
  map_id V := by
    apply ModuleCat.hom_ext
    ext s
    exact D.sectionRestriction_self V.unop s
  map_comp {V W Z} h k := by
    apply ModuleCat.hom_ext
    ext s
    exact (D.sectionRestriction_comp h.unop.le k.unop.le s).symm

def tuplePresheaf (U : ι → X.Opens) (M : ι → X.Modules) : TopCat.Presheaf (Type u) X where
  obj V := Tuple U M V.unop
  map h := TypeCat.ofHom (tupleRestriction h.unop.le)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact tupleRestriction_self V.unop s
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (tupleRestriction_comp h.unop.le k.unop.le s).symm

theorem tuplePresheaf_isSheaf : (tuplePresheaf U M).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  have hcoord (i : ι) : ∃! t : Γ(M i, (iSup V) ⊓ U i), ∀ a,
      (M i).presheaf.map (homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i)))).op t = s a i := by
    let F : TopCat.Sheaf AddCommGrpCat X := ⟨(M i).presheaf, (M i).isSheaf⟩
    apply F.existsUnique_gluing' (fun a => V a ⊓ U i) ((iSup V) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i))))
    · intro x hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx.1
      exact Opens.mem_iSup.mpr ⟨a, ha, hx.2⟩
    · intro a b
      let Z := (V a ⊓ U i) ⊓ (V b ⊓ U i)
      have hz : Z ≤ (V a ⊓ V b) ⊓ U i :=
        le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right)
      have he := congrArg (fun t : Tuple U M (V a ⊓ V b) => t i) (hs a b)
      have hr := congrArg ((M i).presheaf.map (homOfLE hz).op) he
      exact (restriction_comp (M i) _ _ _).symm.trans
        (hr.trans (restriction_comp (M i) _ _ _))
  choose t ht hu using hcoord
  refine ⟨t, ?_, ?_⟩
  · intro a
    funext i
    exact ht i a
  · intro q hq
    funext i
    exact hu i (q i) (fun a => congrFun (hq a) i)

theorem mem_sections_of_locally {V : X.Opens} {α : Type u}
    (W : α → X.Opens) (hW : ∀ a, W a ≤ V) (hcover : V ≤ iSup W)
    (s : Tuple U M V) (hs : ∀ a, tupleRestriction (hW a) s ∈ D.sections (W a)) :
    s ∈ D.sections V := by
  intro i j
  let Z := (V ⊓ U i) ⊓ U j
  let Q := fun a => (W a ⊓ U i) ⊓ U j
  have hQ (a : α) : Q a ≤ Z := inf_le_inf (inf_le_inf (hW a) (le_refl (U i))) (le_refl (U j))
  have hc : Z ≤ iSup Q := by
    intro z hz
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcover hz.1.1)
    exact Opens.mem_iSup.mpr ⟨a, ⟨ha, hz.1.2⟩, hz.2⟩
  let Fj : TopCat.Sheaf AddCommGrpCat X := ⟨(M j).presheaf, (M j).isSheaf⟩
  apply Fj.eq_of_locally_eq' Q Z (fun a => homOfLE (hQ a)) hc
  intro a
  have hi : (M i).presheaf.map (homOfLE (show Q a ≤ W a ⊓ U i from inf_le_left)).op
      (tupleRestriction (hW a) s i) =
    (M i).presheaf.map (homOfLE (hQ a)).op
      ((M i).presheaf.map (homOfLE (show Z ≤ V ⊓ U i from inf_le_left)).op (s i)) := by
    exact (restriction_comp (M i) _ _ _).trans (restriction_comp (M i) _ _ _).symm
  have hj : (M j).presheaf.map (homOfLE (show Q a ≤ W a ⊓ U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (tupleRestriction (hW a) s j) =
    (M j).presheaf.map (homOfLE (hQ a)).op
      ((M j).presheaf.map (homOfLE (show Z ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)) := by
    exact (restriction_comp (M j) _ _ _).trans (restriction_comp (M j) _ _ _).symm
  exact (D.natural Z (Q a) (hQ a) i j _ _ _).symm.trans
    ((congrArg (D.compare (Q a) i j _ _) hi.symm).trans ((hs a i j).trans hj))

def sectionTypePresheaf : TopCat.Presheaf (Type u) X :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj D.modulePresheaf ⋙ forget AddCommGrpCat

theorem sectionTypePresheaf_isSheaf : D.sectionTypePresheaf.IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  change ∀ a b, D.sectionRestriction (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
    D.sectionRestriction (show V a ⊓ V b ≤ V b from inf_le_right) (s b) at hs
  have hv : (tuplePresheaf U M).IsCompatible V (fun a => (s a).val) := by
    intro a b
    exact congrArg Subtype.val (hs a b)
  obtain ⟨t, ht, hu⟩ := (tuplePresheaf_isSheaf (U := U) (M := M)).isSheafUniqueGluing_types
    (fun a => (s a).val) hv
  have hmem : t ∈ D.sections (iSup V) := D.mem_sections_of_locally V (fun a => le_iSup V a)
    le_rfl t (fun a => (ht a).symm ▸ (s a).property)
  refine ⟨⟨t, hmem⟩, ?_, ?_⟩
  · intro a
    exact Subtype.ext (ht a)
  · intro q hq
    apply Subtype.ext
    exact hu q.val (fun a => congrArg Subtype.val (hq a))

/-- The actual module object formed by matching local sections. -/
def moduleSheaf : X.Modules where
  val := D.modulePresheaf
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat) _).mpr
    D.sectionTypePresheaf_isSheaf

end OpenModuleTransitions

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf
