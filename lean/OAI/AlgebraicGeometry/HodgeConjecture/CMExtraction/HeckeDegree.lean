import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Hecke Degree -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeDegree.Local

noncomputable section

/-! A group character trivial on the integral level grades the actual
spherical kernels. Products multiply degrees; raw kernels have the
inverse degree of their double-coset representative. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

variable {G C : Type*} [Group G] [CommGroup C] (U : Subgroup G)
  (d : G →* C) (hd : ∀ u ∈ U, d u = 1)

def heckeCosetDegree : G ⧸ U → C :=
  Quotient.lift d (by
    intro g h hgh
    have h := hd (g⁻¹ * h) (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [map_mul, map_inv, inv_mul_eq_one] using h)

theorem heckeCosetDegree_smul (g : G) (x : G ⧸ U) :
    heckeCosetDegree U d hd (g • x) = d g * heckeCosetDegree U d hd x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact map_mul d g h

def heckeDegreeSpace (c : C) : Submodule ℚ (AbelianScheme.TateComparison.HeckeKernel.CosetModule U) :=
  Finsupp.supported ℚ ℚ {x | heckeCosetDegree U d hd x = c}

theorem heckeDegreeSpace_translate (g : G) {c : C} {w : AbelianScheme.TateComparison.HeckeKernel.CosetModule U}
    (hw : w ∈ heckeDegreeSpace U d hd c) :
    AbelianScheme.TateComparison.HeckeKernel.translate U g w ∈ heckeDegreeSpace U d hd (d g * c) := by
  have hle : heckeDegreeSpace U d hd c ≤
      (heckeDegreeSpace U d hd (d g * c)).comap (AbelianScheme.TateComparison.HeckeKernel.translate U g) := by
    rw [heckeDegreeSpace, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro w ⟨x, hx, rfl⟩
    change AbelianScheme.TateComparison.HeckeKernel.translate U g (Finsupp.single x 1) ∈ heckeDegreeSpace U d hd (d g * c)
    rw [AbelianScheme.TateComparison.HeckeKernel.translate_single]
    apply Finsupp.single_mem_supported ℚ 1
    change heckeCosetDegree U d hd (g • x) = d g * c
    rw [heckeCosetDegree_smul, hx]
  exact hle hw

def IsHomogeneousHecke (T : AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U) (c : C) : Prop :=
  AbelianScheme.TateComparison.HeckeKernel.kernel U T ∈ heckeDegreeSpace U d hd c

theorem homogeneousHecke_action {T : AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U} {a b : C}
    (hT : IsHomogeneousHecke U d hd T a) {w : AbelianScheme.TateComparison.HeckeKernel.CosetModule U}
    (hw : w ∈ heckeDegreeSpace U d hd b) :
    T.val w ∈ heckeDegreeSpace U d hd (a * b) := by
  have hle : heckeDegreeSpace U d hd b ≤ (heckeDegreeSpace U d hd (a * b)).comap T.val := by
    rw [heckeDegreeSpace, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro w ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change d g = b at hx
    change T.val (Finsupp.single (QuotientGroup.mk g) 1) ∈ heckeDegreeSpace U d hd (a * b)
    rw [AbelianScheme.TateComparison.HeckeKernel.hecke_single]
    simpa only [hx, mul_comm b a] using heckeDegreeSpace_translate U d hd g hT
  exact hle hw

theorem homogeneousHecke_mul {T S : AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U} {a b : C}
    (hT : IsHomogeneousHecke U d hd T a) (hS : IsHomogeneousHecke U d hd S b) :
    IsHomogeneousHecke U d hd (T * S) (a * b) :=
  homogeneousHecke_action U d hd hT hS

theorem homogeneousHecke_one : IsHomogeneousHecke U d hd 1 1 := by
  apply Finsupp.single_mem_supported ℚ 1
  exact map_one d

theorem homogeneousHecke_pow {T : AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U} {a : C}
    (hT : IsHomogeneousHecke U d hd T a) (n : ℕ) :
    IsHomogeneousHecke U d hd (T ^ n) (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using homogeneousHecke_one U d hd
  | succ n hn =>
    simpa only [pow_succ] using homogeneousHecke_mul U d hd hn hT

theorem rawHecke_homogeneous {g : G} {T : AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U} (hT : AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset U g T) :
    IsHomogeneousHecke U d hd T (d g)⁻¹ := by
  apply (Finsupp.mem_supported' ℚ _).mpr
  intro x hx
  rw [AbelianScheme.TateComparison.HeckeKernel.raw_kernel_at U hT, ite_eq_right]
  rintro ⟨u, rfl⟩
  apply hx
  change heckeCosetDegree U d hd (u.val • QuotientGroup.mk g⁻¹) = (d g)⁻¹
  rw [heckeCosetDegree_smul, hd u.val u.property, one_mul]
  exact map_inv d g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeDegree.Local
