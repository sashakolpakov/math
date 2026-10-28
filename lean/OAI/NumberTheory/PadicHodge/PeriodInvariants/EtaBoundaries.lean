import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles

/-! # Eta Boundaries -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries

noncomputable section

/-!
# Boundaries after eta

A scaled cycle becomes an eta boundary precisely when its original
cohomology class is killed by the scalar. This is the algebraic step
behind the torsion-removal formula for eta cohomology.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles

variable {R : Type u} [CommRing R] (a : R)

def toCycles (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    C.X n →ₗ[R] EtaCycles.cycles C (n + 1) :=
  (C.d n (n + 1)).hom.codRestrict _ (EtaComplex.d_squared C n)

def etaToCycles (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    EtaComplex.term a C n →ₗ[R] EtaCycles.etaCycles a C (n + 1) :=
  (EtaComplex.differential a C n).codRestrict _
    (fun x => DFunLike.congr_fun (EtaComplex.differential_squared a C n) x)

theorem scaleCycles_mem_boundary_iff (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) (x : EtaCycles.cycles C (n + 1)) :
    EtaCycles.scaleCycles a C (n + 1) x ∈ LinearMap.range (etaToCycles a C n) ↔
      a • x ∈ LinearMap.range (toCycles C n) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨⟨y, hy⟩, _⟩ := (EtaComplex.mem_term a C n b).mp b.property
    have hb' : C.d n (n + 1) b = a ^ (n + 1) • (x : C.X (n + 1)) :=
      congrArg (fun z : EtaCycles.etaCycles a C (n + 1) => (z.val : C.X (n + 1))) hb
    have hdy : C.d n (n + 1) y = a • (x : C.X (n + 1)) := by
      apply ha.pow n
      change a ^ n • C.d n (n + 1) y = a ^ n • (a • (x : C.X (n + 1)))
      rw [← map_smul, hy, hb', pow_succ, mul_smul]
    exact ⟨y, Subtype.ext hdy⟩
  · rintro ⟨y, hy⟩
    have hdy : C.d n (n + 1) y = a • (x : C.X (n + 1)) :=
      congrArg (fun z : EtaCycles.cycles C (n + 1) => (z : C.X (n + 1))) hy
    have hb : a ^ n • y ∈ EtaComplex.term a C n := by
      apply (EtaComplex.mem_term a C n _).mpr
      refine ⟨⟨y, rfl⟩, ⟨x, ?_⟩⟩
      rw [map_smul, hdy, pow_succ, mul_smul]
    refine ⟨⟨a ^ n • y, hb⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change C.d n (n + 1) (a ^ n • y) = a ^ (n + 1) • (x : C.X (n + 1))
    rw [map_smul, hdy, pow_succ, mul_smul]

theorem scaleCycles_preserves_boundaries (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) :
    LinearMap.range (toCycles C n) ≤
      (LinearMap.range (etaToCycles a C n)).comap (EtaCycles.scaleCycles a C (n + 1)) := by
  intro x hx
  exact (scaleCycles_mem_boundary_iff a C n ha x).mpr
    ((LinearMap.range (toCycles C n)).smul_mem a hx)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries
