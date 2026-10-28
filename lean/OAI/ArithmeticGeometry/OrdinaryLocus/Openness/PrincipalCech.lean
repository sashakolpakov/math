import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalOverlaps

/-! # Principal Cech -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCech.Construction

noncomputable section

/-! Additive Čech cocycles for finite principal covers of an affine scheme. -/

open scoped TensorProduct

universe u v w

variable (R : Type u) [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ι → R) (M : Type w) [AddCommGroup M] [Module R M]

abbrev principalCechC0 := ∀ i, Localization.Away (f i) ⊗[R] M
abbrev principalCechC1 := ∀ i j, Localization.Away (f i * f j) ⊗[R] M
abbrev principalCechC2 := ∀ i j k, Localization.Away (f i * (f j * f k)) ⊗[R] M

def principalCechD0 : principalCechC0 R f M →ₗ[R] principalCechC1 R f M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    PrincipalOverlaps.Construction.principalRestrictionModule R M (f j) (f i * f j) (dvd_mul_left _ _) ∘ₗ LinearMap.proj j -
      PrincipalOverlaps.Construction.principalRestrictionModule R M (f i) (f i * f j) (dvd_mul_right _ _) ∘ₗ LinearMap.proj i

def principalCechD1 : principalCechC1 R f M →ₗ[R] principalCechC2 R f M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    PrincipalOverlaps.Construction.principalRestrictionModule R M (f j * f k) (f i * (f j * f k)) (dvd_mul_left _ _) ∘ₗ
        LinearMap.proj k ∘ₗ LinearMap.proj j -
      PrincipalOverlaps.Construction.principalRestrictionModule R M (f i * f k) (f i * (f j * f k))
        (by use f j; ring) ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i +
      PrincipalOverlaps.Construction.principalRestrictionModule R M (f i * f j) (f i * (f j * f k))
        (by use f k; ring) ∘ₗ LinearMap.proj j ∘ₗ LinearMap.proj i

def principalCechEquiv1 : FiniteCoverCocycles.Construction.finiteCoverC1 R (fun i ↦ Localization.Away (f i)) M ≃ₗ[R]
    principalCechC1 R f M :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
    PrincipalOverlaps.Construction.principalOverlapModuleEquiv R (f i) (f j) M

def principalCechEquiv2 : FiniteCoverCocycles.Construction.finiteCoverC2 R (fun i ↦ Localization.Away (f i)) M ≃ₗ[R]
    principalCechC2 R f M :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
    LinearEquiv.piCongrRight fun k ↦ PrincipalOverlaps.Construction.principalTripleModuleEquiv R M (f i) (f j) (f k)

omit [Fintype ι] [DecidableEq ι] in
theorem principalCechD0_comparison (x : principalCechC0 R f M) :
    principalCechD0 R f M x =
      principalCechEquiv1 R f M (FiniteCoverCocycles.Construction.finiteCoverD0 R (fun i ↦ Localization.Away (f i)) M x) := by
  funext i j
  simp [principalCechD0, principalCechEquiv1, FiniteCoverCocycles.Construction.finiteCoverD0,
    PrincipalOverlaps.Construction.principalOverlapModuleEquiv_insert_left, PrincipalOverlaps.Construction.principalOverlapModuleEquiv_insert_right]

omit [Fintype ι] [DecidableEq ι] in
theorem principalCechD1_comparison
    (z : FiniteCoverCocycles.Construction.finiteCoverC1 R (fun i ↦ Localization.Away (f i)) M) :
    principalCechD1 R f M (principalCechEquiv1 R f M z) =
      principalCechEquiv2 R f M (FiniteCoverCocycles.Construction.finiteCoverD1 R (fun i ↦ Localization.Away (f i)) M z) := by
  funext i j k
  simp [principalCechD1, principalCechEquiv1, principalCechEquiv2, FiniteCoverCocycles.Construction.finiteCoverD1,
    PrincipalOverlaps.Construction.principalTripleModuleEquiv_insert_first, PrincipalOverlaps.Construction.principalTripleModuleEquiv_insert_middle,
    PrincipalOverlaps.Construction.principalTripleModuleEquiv_insert_last]

theorem principalCechD1_comp_D0 : principalCechD1 R f M ∘ₗ principalCechD0 R f M = 0 := by
  apply LinearMap.ext
  intro x
  change principalCechD1 R f M (principalCechD0 R f M x) = 0
  rw [principalCechD0_comparison, principalCechD1_comparison]
  have h := LinearMap.congr_fun
    (FiniteCoverCocycles.Construction.finiteCoverD1_comp_D0 R (fun i ↦ Localization.Away (f i)) M) x
  change FiniteCoverCocycles.Construction.finiteCoverD1 R (fun i ↦ Localization.Away (f i)) M
    (FiniteCoverCocycles.Construction.finiteCoverD0 R (fun i ↦ Localization.Away (f i)) M x) = 0 at h
  rw [h, map_zero]

theorem principalCech_exact_degreeOne (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (principalCechD0 R f M) (principalCechD1 R f M) := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := (principalCechEquiv1 R f M).surjective z
    rw [principalCechD1_comparison] at hz
    have hw : FiniteCoverCocycles.Construction.finiteCoverD1 R (fun i ↦ Localization.Away (f i)) M w = 0 :=
      (principalCechEquiv2 R f M).injective (hz.trans (map_zero _).symm)
    obtain ⟨x, hx⟩ := FiniteCoverCocycles.Construction.principalCover_cocycle_is_coboundary R M f hf w hw
    refine ⟨x, ?_⟩
    rw [principalCechD0_comparison, hx]
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (principalCechD1_comp_D0 R f M) x

theorem principalCech_sections_glue (hf : Ideal.span (Set.range f) = ⊤)
    (x : principalCechC0 R f M) (hx : principalCechD0 R f M x = 0) :
    ∃! m, FiniteCoverCocycles.Construction.finiteCoverUnit R (fun i ↦ Localization.Away (f i)) M m = x := by
  rw [principalCechD0_comparison] at hx
  apply FiniteCoverCocycles.Construction.principalCover_sections_glue R M f hf x
  exact (principalCechEquiv1 R f M).injective (hx.trans (map_zero _).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCech.Construction
