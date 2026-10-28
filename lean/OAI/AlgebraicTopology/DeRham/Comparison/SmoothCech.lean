import OAI.Analysis.DifferentialForms.Manifold.SmoothFormD
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Data.Fin.Tuple.Basic

/-! # Smooth Cech -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech

noncomputable section

/-!
# Čech cochains of the genuine smooth-form sheaf

Cochains are families of actual sections on finite intersections of open
sets. Restricting along tuple precomposition gives a cosimplicial module;
mathlib's alternating-coface construction proves that the signed Čech
differential squares to zero. No acyclicity or comparison theorem is assumed.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped Simplicial BigOperators

universe u

section Intersections

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)

/-- The finite open intersection belonging to a Čech tuple. -/
def cechIntersection {n : ℕ} (a : Fin (n + 1) → ι) : Opens X :=
  ⨅ k, U (a k)

/-- This finite infimum is the ordinary intersection of the indicated open sets. -/
@[simp]
theorem mem_cechIntersection {n : ℕ} (a : Fin (n + 1) → ι) (x : X) :
    x ∈ cechIntersection U a ↔ ∀ k, x ∈ U (a k) := by
  change x ∈ ((⨅ k, U (a k) : Opens X) : Set X) ↔ _
  rw [Opens.coe_iInf]
  exact Set.mem_iInter

theorem cechIntersection_le {n : ℕ} (a : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    cechIntersection U a ≤ U (a k) :=
  iInf_le _ k

/-- Forgetting or repeating entries only enlarges the intersection. -/
theorem cechIntersection_le_precomp {n m : ℕ} (a : Fin (m + 1) → ι)
    (f : Fin (n + 1) → Fin (m + 1)) :
    cechIntersection U a ≤ cechIntersection U (a ∘ f) :=
  le_iInf (fun k => cechIntersection_le U a (f k))

/-- Inserting an initial index intersects the previous domain with its open set. -/
theorem cechIntersection_cons {n : ℕ} (i : ι) (a : Fin (n + 1) → ι) :
    cechIntersection U (Fin.cons i a) = U i ⊓ cechIntersection U a := by
  apply le_antisymm
  · apply le_inf
    · exact cechIntersection_le U (Fin.cons i a) 0
    · exact le_iInf (fun k => cechIntersection_le U (Fin.cons i a) k.succ)
  · apply le_iInf
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact inf_le_left
    · exact inf_le_right.trans (cechIntersection_le U a j)

end Intersections

section Presheaf

variable {X ι : Type u} [TopologicalSpace X]
variable (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) (U : ι → Opens X)

/-- Actual sections of a presheaf on all intersections of n+1 cover members. -/
abbrev CechCochain (n : ℕ) :=
  (a : Fin (n + 1) → ι) → F.obj (op (cechIntersection U a))

/-- Restriction along a tuple-index map, applied to genuine sections. -/
def cechPrecomp {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) :
    CechCochain F U n →ₗ[ℂ] CechCochain F U m where
  toFun c a := (F.map (homOfLE (cechIntersection_le_precomp U a f)).op).hom
    (c (a ∘ f))
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

/-- The Čech cosimplicial module of the given presheaf and open family. -/
def cechCosimplicial : CosimplicialObject (ModuleCat.{u} ℂ) where
  obj n := ModuleCat.of ℂ (CechCochain F U n.len)
  map f := ModuleCat.ofHom (cechPrecomp F U f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (cechIntersection_le_precomp U a id)).op).hom (c a) = c a
    rw [show (homOfLE (cechIntersection_le_precomp U a id)).op =
      𝟙 (op (cechIntersection U a)) from Subsingleton.elim _ _]
    exact congrArg (fun k => k.hom (c a)) (F.map_id (op (cechIntersection U a)))
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (cechIntersection_le_precomp U a
      (g.toOrderHom ∘ f.toOrderHom))).op).hom (c (a ∘ g.toOrderHom ∘ f.toOrderHom)) =
      (F.map (homOfLE (cechIntersection_le_precomp U a g.toOrderHom)).op).hom
        ((F.map (homOfLE (cechIntersection_le_precomp U (a ∘ g.toOrderHom)
          f.toOrderHom)).op).hom (c (a ∘ g.toOrderHom ∘ f.toOrderHom)))
    rw [show (homOfLE (cechIntersection_le_precomp U a
      (g.toOrderHom ∘ f.toOrderHom))).op =
        (homOfLE (cechIntersection_le_precomp U (a ∘ g.toOrderHom) f.toOrderHom)).op ≫
        (homOfLE (cechIntersection_le_precomp U a g.toOrderHom)).op
      from Subsingleton.elim _ _, F.map_comp]
    rfl

/-- The actual Čech cochain complex, with the alternating restriction differential. -/
def cechComplex : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cechCosimplicial F U)

/-- The signed Čech differential as a linear map on the explicit section families. -/
def cechDelta (n : ℕ) : CechCochain F U n →ₗ[ℂ] CechCochain F U (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial F U) n).hom

/-- The differential is the usual alternating sum of restrictions with one
index omitted at a time. -/
theorem cechDelta_apply (n : ℕ) (c : CechCochain F U n)
    (a : Fin (n + 2) → ι) :
    cechDelta F U n c a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        (F.map (homOfLE (cechIntersection_le_precomp U a j.succAbove)).op).hom
          (c (a ∘ j.succAbove)) := by
  classical
  simp only [cechDelta, AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  change ((∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    cechPrecomp F U j.succAbove) c) a = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rfl

theorem cechDelta_squared (n : ℕ) (c : CechCochain F U n) :
    cechDelta F U (n + 1) (cechDelta F U n c) = 0 := by
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (cechCosimplicial F U) n
  exact congrArg (fun f => f.hom c) h

/-- The bundled cochain differential is exactly the explicit signed map. -/
theorem cechComplex_d (n : ℕ) :
    (cechComplex F U).d n (n + 1) = ModuleCat.ofHom (cechDelta F U n) := by
  exact CochainComplex.of_d
    (fun k => (cechCosimplicial F U).obj ⦋k⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial F U)) n

variable {κ : Type u} (V : κ → Opens X) (r : κ → ι)
  (hr : ∀ k, V k ≤ U (r k))

include hr in
/-- A refinement of open families gives inclusions on every finite intersection. -/
theorem cechIntersection_refinement_le {n : ℕ} (a : Fin (n + 1) → κ) :
    cechIntersection V a ≤ cechIntersection U (r ∘ a) :=
  le_iInf (fun k => (cechIntersection_le V a k).trans (hr (a k)))

/-- The actual section restriction associated to a refinement of the open family. -/
def cechRefinementMap (n : ℕ) : CechCochain F U n →ₗ[ℂ] CechCochain F V n where
  toFun c a := (F.map (homOfLE (cechIntersection_refinement_le U V r hr a)).op).hom
    (c (r ∘ a))
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

omit U V r hr in
/-- Functoriality of actual presheaf restrictions, in the section notation. -/
theorem cechSection_restrict_trans {A B C : Opens X} (hBA : B ≤ A) (hCB : C ≤ B)
    (s : F.obj (op A)) :
    (F.map (homOfLE hCB).op).hom ((F.map (homOfLE hBA).op).hom s) =
      (F.map (homOfLE (hCB.trans hBA)).op).hom s := by
  exact (congrArg (fun k => k.hom s) (F.map_comp (homOfLE hBA).op (homOfLE hCB).op)).symm

/-- Refinement restriction is natural for all cosimplicial operators. -/
def cechRefinementNat : cechCosimplicial F U ⟶ cechCosimplicial F V where
  app n := ModuleCat.ofHom (cechRefinementMap F U V r hr n.len)
  naturality n m f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (F.map (homOfLE (cechIntersection_refinement_le U V r hr a)).op).hom
        ((F.map (homOfLE (cechIntersection_le_precomp U (r ∘ a) f.toOrderHom)).op).hom
          (c (r ∘ a ∘ f.toOrderHom))) =
      (F.map (homOfLE (cechIntersection_le_precomp V a f.toOrderHom)).op).hom
        ((F.map (homOfLE (cechIntersection_refinement_le U V r hr
          (a ∘ f.toOrderHom))).op).hom (c (r ∘ a ∘ f.toOrderHom)))
    rw [cechSection_restrict_trans, cechSection_restrict_trans]

/-- The induced map of actual Čech complexes under a cover refinement. -/
def cechRefinement : cechComplex F U ⟶ cechComplex F V :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (cechRefinementNat F U V r hr)

@[simp]
theorem cechRefinement_f (n : ℕ) :
    (cechRefinement F U V r hr).f n = ModuleCat.ofHom (cechRefinementMap F U V r hr n) := rfl

/-- Refinement commutes with the signed differential on the nose. -/
theorem cechRefinementMap_delta (n : ℕ) (c : CechCochain F U n) :
    cechRefinementMap F U V r hr (n + 1) (cechDelta F U n c) =
      cechDelta F V n (cechRefinementMap F U V r hr n c) := by
  have h := (cechRefinement F U V r hr).comm n (n + 1)
  rw [cechComplex_d, cechComplex_d, cechRefinement_f, cechRefinement_f] at h
  exact (congrArg (fun k => k.hom c) h).symm

end Presheaf

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E) (p : ℕ)

/-- Čech cochains of the actual smooth p-form sheaf. -/
abbrev SmoothCechCochain (n : ℕ) := CechCochain (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U n

/-- The Čech complex of genuine smooth p-forms. -/
abbrev smoothCechComplex := cechComplex (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U

/-- The actual signed Čech differential on smooth-form families. -/
abbrev smoothCechDelta (n : ℕ) := cechDelta (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U n

/-- The usual signed restriction formula, now in the concrete smooth-form API. -/
theorem smoothCechDelta_apply (n : ℕ) (c : SmoothCechCochain U p n)
    (a : Fin (n + 2) → ι) :
    smoothCechDelta U p n c a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (cechIntersection_le_precomp U a j.succAbove)
          (c (a ∘ j.succAbove)) :=
  cechDelta_apply (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U n c a

theorem smoothCechDelta_squared (n : ℕ) (c : SmoothCechCochain U p n) :
    smoothCechDelta U p (n + 1) (smoothCechDelta U p n c) = 0 :=
  cechDelta_squared (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U n c

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
