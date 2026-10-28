import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex
import Mathlib.Tactic.Abel

/-! # Coordinate Split -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.CoordinateSplit

noncomputable section

/-! Splitting an exterior power into the terms containing or omitting a
chosen coordinate. This is the degreewise algebra for the Koszul cone. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
  (l : Module.Dual R V) (e : V)

def projection : Module.End R V := LinearMap.id - (LinearMap.toSpanSingleton R V e).comp l

theorem projection_apply (v : V) : projection R V l e v = v - l v • e := rfl

theorem ambient_projection (x : ExteriorAlgebra R V) :
    ExteriorAlgebra.map (projection R V l e) x =
      x - ExteriorAlgebra.ι R e * AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a =>
      simp [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
      simp only [map_add, hx, hy, mul_add]
      abel
  | ι_mul x v hx =>
      change ExteriorAlgebra.map (projection R V l e) (ExteriorAlgebra.ι R v * x) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι, projection_apply, map_sub, map_smul,
        hx, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul]
      have hswap : ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R e *
          AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x) =
          -(ExteriorAlgebra.ι R e * (ExteriorAlgebra.ι R v * AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x)) := by
        rw [← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v e),
          neg_mul, mul_assoc]
      have hsquare : ExteriorAlgebra.ι R e * (ExteriorAlgebra.ι R e *
          AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x) = 0 := by
        rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
      simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, hswap, hsquare,
        smul_zero, sub_zero]
      abel

theorem map_projection (n : ℕ) (x : ⋀[R]^(n + 1) V) :
    exteriorPower.map (n + 1) (projection R V l e) x =
      x - AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n x) := by
  apply Subtype.ext
  rw [KoszulComplex.map_coe, ambient_projection]
  rfl

theorem contraction_projection (n : ℕ) (x : ⋀[R]^(n + 1) V) :
    exteriorPower.map n (projection R V l e) (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n x) =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n x := by
  apply Subtype.ext
  rw [KoszulComplex.map_coe, ambient_projection]
  change AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x.val - ExteriorAlgebra.ι R e *
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x.val) = _
  rw [show AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x.val) = 0 from
    CliffordAlgebra.contractLeft_contractLeft l x.val, mul_zero, sub_zero]
  rfl

variable (W : Type u) [AddCommGroup W] [Module R W]
  (f : W →ₗ[R] V) (g : V →ₗ[R] W)
  (hgf : g.comp f = LinearMap.id) (hfg : f.comp g = projection R V l e)
  (hle : l e = 1) (hlf : l.comp f = 0) (hge : g e = 0)

theorem wedge_naturality (n : ℕ) (x : ⋀[R]^n V) :
    exteriorPower.map (n + 1) g (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n x) =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R W (g e) n (exteriorPower.map n g x) := by
  apply Subtype.ext
  rw [KoszulComplex.map_coe, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_coe, map_mul,
    ExteriorAlgebra.map_apply_ι, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_coe, KoszulComplex.map_coe]

include hlf in
theorem contraction_inclusion (n : ℕ) (x : ⋀[R]^(n + 1) W) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n (exteriorPower.map (n + 1) f x) = 0 := by
  have h := LinearMap.congr_fun
    (KoszulComplex.contraction_naturality R W V 0 l f hlf n) x
  have hz : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R W (0 : Module.Dual R W) n x = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_zero (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R W)))) x.val
  simpa only [LinearMap.comp_apply, hz, map_zero] using h

def forward (n : ℕ) : ((⋀[R]^n W) × (⋀[R]^(n + 1) W)) →ₗ[R] (⋀[R]^(n + 1) V) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n).comp (exteriorPower.map n f)).coprod (exteriorPower.map (n + 1) f)

def backward (n : ℕ) : (⋀[R]^(n + 1) V) →ₗ[R] ((⋀[R]^n W) × (⋀[R]^(n + 1) W)) :=
  ((exteriorPower.map n g).comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n)).prod (exteriorPower.map (n + 1) g)

include hfg in
theorem forward_backward (n : ℕ) (x : ⋀[R]^(n + 1) V) :
    forward R V e W f n (backward R V l W g n x) = x := by
  change AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f
    (exteriorPower.map n g (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n x))) +
    exteriorPower.map (n + 1) f (exteriorPower.map (n + 1) g x) = x
  have hm (m : ℕ) (y : ⋀[R]^m V) : exteriorPower.map m f (exteriorPower.map m g y) =
      exteriorPower.map m (projection R V l e) y := by
    change ((exteriorPower.map m f).comp (exteriorPower.map m g)) y = _
    rw [← exteriorPower.map_comp, hfg]
  rw [hm, hm, contraction_projection, map_projection]
  abel

include hgf hle hlf hge in
theorem backward_forward (n : ℕ) (x : (⋀[R]^n W) × (⋀[R]^(n + 1) W)) :
    backward R V l W g n (forward R V e W f n x) = x := by
  apply Prod.ext
  · change exteriorPower.map n g (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f x.1) + exteriorPower.map (n + 1) f x.2)) = x.1
    rw [map_add, contraction_inclusion R V l W f hlf, add_zero]
    have hw : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l n (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f x.1)) =
        exteriorPower.map n f x.1 := by
      cases n with
      | zero => rw [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge_zero, hle, one_smul]
      | succ n =>
          have h := AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge R V l e n (exteriorPower.map (n + 1) f x.1)
          rw [contraction_inclusion R V l W f hlf, map_zero, add_zero, hle, one_smul] at h
          exact h
    rw [hw, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hgf, exteriorPower.map_id]
    rfl
  · change exteriorPower.map (n + 1) g
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R V e n (exteriorPower.map n f x.1) + exteriorPower.map (n + 1) f x.2) = x.2
    rw [map_add, wedge_naturality, hge]
    have hz : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R W (0 : W) n (exteriorPower.map n g (exteriorPower.map n f x.1)) = 0 := by
      apply Subtype.ext
      simp only [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_coe, map_zero, zero_mul, ZeroMemClass.coe_zero]
    rw [hz, zero_add, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hgf, exteriorPower.map_id]
    rfl

def equiv (n : ℕ) : ((⋀[R]^n W) × (⋀[R]^(n + 1) W)) ≃ₗ[R] (⋀[R]^(n + 1) V) where
  __ := forward R V e W f n
  invFun := backward R V l W g n
  left_inv := backward_forward R V l e W f g hgf hle hlf hge n
  right_inv := forward_backward R V l e W f g hfg n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.CoordinateSplit
