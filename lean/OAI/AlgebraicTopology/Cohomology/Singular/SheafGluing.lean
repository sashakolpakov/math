import OAI.AlgebraicTopology.Cohomology.Singular.SheafSections
import Mathlib.Topology.Sheaves.Stalks

/-! # Sheaf Gluing -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing

noncomputable section

/-!
# Gluing cohomology-sheaf sections from agreement of germs

Agreement of local classes is needed only after passing to the actual
cohomology sheaf. In particular no separatedness of the cohomology presheaf
is assumed. A cover of a closed support may be completed by its open
complement, on which a sheaf with zero stalks has only the zero section.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Agreement of germs of actual module-sheaf sections implies compatibility
on the full pairwise intersections. -/
theorem moduleSheaf_compatible_of_germs
    (F : TopCat.Sheaf (ModuleCat.{0} R) X)
    {ι : Type*} (U : ι → Opens X) (s : ∀ i, F.obj.obj (op (U i)))
    (hs : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      F.presheaf.germ (U i) x hi (s i) = F.presheaf.germ (U j) x hj (s j)) :
    TopCat.Presheaf.IsCompatible F.obj U s := by
  intro i j
  apply TopCat.Presheaf.section_ext F (U i ⊓ U j)
  intro x hx
  simpa only [TopCat.Presheaf.germ_res_apply] using hs i j x hx.1 hx.2

/-- Local cochain classes whose image germs agree give a unique global
section of the actual cohomology sheaf. -/
theorem existsUnique_global_sheafCohomologySection_of_germs
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {ι : Type*} (U : ι → Opens X) (hU : iSup U = ⊤) (n : ℕ)
    (a : ∀ i, (SheafSections.sheafSectionCohomologyPresheaf K n).obj (op (U i)))
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (K.homology n).presheaf.germ (U i) x hi (SheafSections.sheafCohomologySectionMap K (U i) n (a i)) =
        (K.homology n).presheaf.germ (U j) x hj (SheafSections.sheafCohomologySectionMap K (U j) n (a j))) :
    ∃! s : (K.homology n).obj.obj (op (⊤ : Opens X)),
      ∀ i, (K.homology n).obj.map (homOfLE (le_top : U i ≤ ⊤)).op s =
        SheafSections.sheafCohomologySectionMap K (U i) n (a i) :=
  (K.homology n).existsUnique_gluing' U ⊤
    (fun i => homOfLE (le_top : U i ≤ ⊤)) (by rw [hU]) _
    (moduleSheaf_compatible_of_germs (K.homology n) U _ ha)

/-- A sheaf with zero stalks on `O` glues local sections covering its closed
support with the zero section on `O`. -/
theorem existsUnique_moduleSheafSection_with_zero
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) (O : Opens X)
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤)
    (s : ∀ i, F.obj.obj (op (U i)))
    (hs : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      F.presheaf.germ (U i) x hi (s i) = F.presheaf.germ (U j) x hj (s j))
    (hzero : ∀ x ∈ O, IsZero (F.presheaf.stalk x)) :
    ∃! t : F.obj.obj (op (⊤ : Opens X)),
      (∀ i, F.obj.map (homOfLE (le_top : U i ≤ ⊤)).op t = s i) ∧
        F.obj.map (homOfLE (le_top : O ≤ ⊤)).op t = 0 := by
  let V : Option ι → Opens X
    | none => O
    | some i => U i
  let tV : (i : Option ι) → F.obj.obj (op (V i))
    | none => 0
    | some i => s i
  have hV : (⊤ : Opens X) ≤ iSup V := by
    calc
      ⊤ = iSup U ⊔ O := hcover.symm
      _ ≤ iSup V := sup_le (iSup_le fun i => le_iSup V (some i)) (le_iSup V none)
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V tV := by
    apply moduleSheaf_compatible_of_germs F V tV
    intro i j x hi hj
    cases i with
    | none =>
      exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hzero x hi)) _ _
    | some i =>
      cases j with
      | none =>
        exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hzero x hj)) _ _
      | some j => exact hs i j x hi hj
  obtain ⟨t, ht, ht_unique⟩ := F.existsUnique_gluing' V ⊤
    (fun i => homOfLE (le_top : V i ≤ ⊤)) hV tV hcompat
  refine ⟨t, ⟨fun i => ht (some i), ht none⟩, ?_⟩
  intro t' ht'
  apply ht_unique t'
  intro i
  cases i with
  | none => exact ht'.2
  | some i => exact ht'.1 i

/-- The germ of a glued global section is exactly the germ of each supplied
local section. -/
theorem globalSection_germ_of_restriction
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) (U : Opens X)
    (t : F.obj.obj (op (⊤ : Opens X))) (s : F.obj.obj (op U))
    (h : F.obj.map (homOfLE (le_top : U ≤ ⊤)).op t = s)
    (x : X) (hx : x ∈ U) :
    F.presheaf.germ ⊤ x (by trivial) t = F.presheaf.germ U x hx s := by
  have h' := congrArg (F.presheaf.germ U x hx) h
  simpa only [TopCat.Presheaf.germ_res_apply] using h'

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing
