import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalInjectionElements
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

/-! # Top Row Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge

noncomputable section

/-! The actual final row of a first-quadrant double complex maps to
total cohomology. The map is defined on the original categorical
homology and retains the sign in the total differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)] (c : ℕ)
  (hc : ∀ q, (K.d c (c + 1)).f q = 0)

local notation "T" => K.total (ComplexShape.up ℕ)

include hc in
omit [K.HasTotal (ComplexShape.up ℕ)] in
theorem outgoing_zero (q : ℕ) (x : (K.X c).X q) :
    (K.d c (c + 1)).f q x = 0 := by
  rw [hc q]
  rfl

private theorem differential_to (q p N N' : ℕ) (hN : q + p = N) (hnext : N + 1 = N')
    (x : (K.X q).X p) :
    (T).d N N' (K.ιTotal (.up ℕ) q p N hN x) =
      K.ιTotal (.up ℕ) (q + 1) p N' (by change q + 1 + p = N'; omega)
        ((K.d q (q + 1)).f p x) +
      ((-1 : ℤˣ) ^ q) • K.ιTotal (.up ℕ) q (p + 1) N'
        (by change q + (p + 1) = N'; omega) ((K.X q).d p (p + 1) x) := by
  subst N'
  exact Module.TotalInjectionElements.differential K q p N hN x

def cycleMapTo (n N : ℕ) (hN : c + n = N) : Module.CochainClasses.cycles (K.X c) n →ₗ[R] Module.CochainClasses.cycles T N :=
  (((K.ιTotal (.up ℕ) c n N hN).hom).comp (Module.CochainClasses.cycles (K.X c) n).subtype).codRestrict _
    (fun x => by
      change (T).d N (N + 1) (K.ιTotal (.up ℕ) c n N hN x.val) = 0
      have hx : (K.X c).d n (n + 1) x.val = 0 := x.property
      have h := Module.TotalInjectionElements.differential K c n N hN x.val
      simpa only [outgoing_zero K c hc, hx, map_zero, smul_zero, add_zero] using h)

abbrev cycleMap (n : ℕ) : Module.CochainClasses.cycles (K.X c) n →ₗ[R] Module.CochainClasses.cycles T (c + n) :=
  cycleMapTo K c hc n (c + n) rfl

def onCycles (n : ℕ) : Module.CochainClasses.cycles (K.X c) n →ₗ[R] (T).homology (c + n) :=
  (Module.CochainClasses.classMap T (c + n)).comp (cycleMap K c hc n)

theorem onCycles_eq_zero (n : ℕ) (x : Module.CochainClasses.cycles (K.X c) n)
    (hx : Module.CochainClasses.classMap (K.X c) n x = 0) : onCycles K c hc n x = 0 := by
  cases n with
  | zero =>
      have h := (Module.CochainClasses.classMap_zero_eq_zero_iff (K.X c) x).mp hx
      rw [h, map_zero]
  | succ n =>
      obtain ⟨y, hy⟩ := (Module.CochainClasses.classMap_succ_eq_zero_iff (K.X c) n x).mp hx
      apply (Module.CochainClasses.classMap_eq_zero_iff T (c + (n + 1)) (cycleMap K c hc (n + 1) x)).mpr
      have hprev : (ComplexShape.up ℕ).prev (c + (n + 1)) = c + n := by
        rw [← Nat.add_assoc]
        exact (ComplexShape.up ℕ).prev_eq' rfl
      rw [hprev]
      refine ⟨(-1 : ℤ) ^ c • K.ιTotal (.up ℕ) c n (c + n) rfl y, ?_⟩
      have hd := differential_to K c n (c + n) (c + (n + 1)) rfl (Nat.add_assoc c n 1) y
      simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.coe_neg_one] at hd
      rw [outgoing_zero K c hc, map_zero, zero_add, hy] at hd
      change (T).d (c + n) (c + (n + 1))
        ((-1 : ℤ) ^ c • K.ιTotal (.up ℕ) c n (c + n) rfl y) = _
      rw [map_zsmul, hd, smul_smul, ← mul_pow]
      norm_num
      rfl

private theorem boundary_le_kernel (n : ℕ) :
    Module.CochainClasses.boundaries (K.X c) n ≤ (onCycles K c hc n).ker := by
  intro x hx
  apply onCycles_eq_zero K c hc n x
  have hq : (Module.CochainClasses.boundaries (K.X c) n).mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero (Module.CochainClasses.boundaries (K.X c) n)).mpr hx
  change (Module.CochainClasses.quotientIso (K.X c) n).inv.hom ((Module.CochainClasses.boundaries (K.X c) n).mkQ x) = 0
  rw [hq, map_zero]

def map (n : ℕ) : (K.X c).homology n →ₗ[R] (T).homology (c + n) :=
  ((Module.CochainClasses.boundaries (K.X c) n).liftQ (onCycles K c hc n) (boundary_le_kernel K c hc n)).comp
    (Module.CochainClasses.quotientIso (K.X c) n).hom.hom

theorem map_class (n : ℕ) (x : Module.CochainClasses.cycles (K.X c) n) :
    map K c hc n (Module.CochainClasses.classMap (K.X c) n x) = Module.CochainClasses.classMap T (c + n) (cycleMap K c hc n x) := by
  change (Module.CochainClasses.boundaries (K.X c) n).liftQ (onCycles K c hc n) (boundary_le_kernel K c hc n)
    ((Module.CochainClasses.quotientIso (K.X c) n).hom ((Module.CochainClasses.quotientIso (K.X c) n).inv
      ((Module.CochainClasses.boundaries (K.X c) n).mkQ x))) = _
  rw [Iso.inv_hom_id_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge
