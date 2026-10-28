import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionHom
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-! # Hom Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomComplex.Ext

noncomputable section

/-! Hom from a fixed object preserves acyclic nonnegative complexes of Ext-acyclic objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite
open ZeroObject

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℕ)

def nonnegativeHomComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K

omit [HasExt C] in
theorem acyclic_initial_mono (hK : K.Acyclic) : Mono (K.d 0 1) := by
  have h := (K.exactAt_iff' 0 0 1 (by simp) (by simp)).mp (hK 0)
  exact h.mono_g (K.shape 0 0 (by decide))

theorem acyclic_hom_lift (hK : K.Acyclic)
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (n : ℕ) (z : A ⟶ K.X (n + 1)) (hz : z ≫ K.d (n + 1) (n + 2) = 0) :
    ∃ y : A ⟶ K.X n, y ≫ K.d n (n + 1) = z := by
  have : Mono (K.d 0 1) := acyclic_initial_mono K hK
  let e : (0 : C) ⟶ K.X 0 := 0
  have he : e ≫ K.d 0 1 = 0 := zero_comp
  have haug : (ShortComplex.mk e (K.d 0 1) he).Exact :=
    ((ShortComplex.mk e (K.d 0 1) he).exact_iff_mono rfl).mpr inferInstance
  have hpos (p : ℕ) : (ResolutionCycles.Ext.resolutionSequence K p).Exact :=
    (K.exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp (hK (p + 1))
  have hzero (q : ℕ) : Subsingleton (Ext A (0 : C) (q + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero
      ((extFunctorObj A (q + 1)).map_isZero (isZero_zero C))
  exact ResolutionHom.Ext.acyclicResolution_hom_exact_succ A K e he haug hpos hzero hExt n z hz

theorem nonnegativeHomComplex_acyclic (hK : K.Acyclic)
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) :
    (nonnegativeHomComplex A K).Acyclic := by
  let H := preadditiveCoyoneda.obj (op A)
  let L := nonnegativeHomComplex A K
  intro n
  cases n with
  | zero =>
    have : Mono (K.d 0 1) := acyclic_initial_mono K hK
    have hzero : (L.sc' 0 0 1).f = 0 := by
      change H.map (K.d 0 0) = 0
      rw [K.shape 0 0 (by decide), H.map_zero]
    apply (L.exactAt_iff' 0 0 1 (by simp) (by simp)).mpr
    apply ((L.sc' 0 0 1).exact_iff_mono hzero).mpr
    change Mono (H.map (K.d 0 1))
    infer_instance
  | succ n =>
    apply ((nonnegativeHomComplex A K).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mpr
    rw [ShortComplex.ab_exact_iff]
    intro z hz
    exact acyclic_hom_lift A K hK hExt n z hz

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomComplex.Ext
