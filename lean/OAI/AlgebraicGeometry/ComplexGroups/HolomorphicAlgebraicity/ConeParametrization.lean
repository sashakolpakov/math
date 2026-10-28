import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage

/-! # Cone Parametrization -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone

noncomputable section

/-!
# Lifting projective parametrizations to the punctured cone
-/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

def normalizedLift (i : ι) (u : {j : ι // j ≠ i} → ℂ) : ι → ℂ :=
  fun j => if h : j = i then 1 else u ⟨j, h⟩

omit [Fintype ι] in
theorem normalizedLift_self (i : ι) (u : {j : ι // j ≠ i} → ℂ) : normalizedLift i u i = 1 := by
  simp [normalizedLift]

theorem differentiable_normalizedLift (i : ι) : Differentiable ℂ (normalizedLift i) := by
  apply differentiable_pi.mpr
  intro j
  by_cases hj : j = i
  · simp only [normalizedLift, dite_eq_left hj]
    exact differentiable_const _
  · simp only [normalizedLift, dite_eq_right hj]
    exact differentiable_apply _

omit [Fintype ι] in
theorem ratios_smul_normalizedLift (i : ι) (u : {j : ι // j ≠ i} → ℂ)
    {t : ℂ} (ht : t ≠ 0) : CoordinateCone.Constructions.Cone.coordinateRatios i (t • normalizedLift i u) = u := by
  ext j
  simp [CoordinateCone.Constructions.Cone.coordinateRatios, normalizedLift, j.property, ht]

omit [Fintype ι] in
theorem smul_normalizedLift_ratios (i : ι) (v : ι → ℂ) (hvi : v i ≠ 0) :
    v i • normalizedLift i (CoordinateCone.Constructions.Cone.coordinateRatios i v) = v := by
  ext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.smul_apply, smul_eq_mul, normalizedLift_self, mul_one]
  · simp only [Pi.smul_apply, smul_eq_mul, normalizedLift, dite_eq_right hj, CoordinateCone.Constructions.Cone.coordinateRatios]
    exact mul_div_cancel₀ _ hvi

theorem local_parametrization_of_coordinateCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (Z : Set (Projectivization ℂ (ι → ℂ)))
    (hparam : ∀ i p, p ∈ Z → p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source →
      ∃ (O : Set ({j : ι // j ≠ i} → ℂ)) (V : Set E) (φ : E → ({j : ι // j ≠ i} → ℂ)),
        IsOpen O ∧ ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i p ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
        ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm ⁻¹' Z) ∩ O ⊆ φ '' V ∧
        MapsTo φ V ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm ⁻¹' Z) ∧ InjOn φ V)
    (v : ι → ℂ) (hv : v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z) (hv0 : v ≠ 0) :
    ∃ (O : Set (ι → ℂ)) (V : Set (E × ℂ)) (φ : E × ℂ → (ι → ℂ)),
      IsOpen O ∧ v ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
      ProjectiveCone.Constructions.Cone.projectiveCone Z ∩ O ⊆ φ '' V ∧ MapsTo φ V (ProjectiveCone.Constructions.Cone.projectiveCone Z) ∧ InjOn φ V := by
  classical
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (Projectivization.mk ℂ v hv0)
  have hvi : v i ≠ 0 := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi
  obtain ⟨O, V, φ, hO, hvO, hV, hφ, hsub, hmaps, hinj⟩ := hparam i _ (hv hv0) hi
  rw [← CoordinateCone.Constructions.Cone.coordinateRatios_eq_projectiveChart i v hv0] at hvO
  let W : Set (ι → ℂ) := {w | w i ≠ 0} ∩ CoordinateCone.Constructions.Cone.coordinateRatios i ⁻¹' O
  have hpatch : IsOpen {w : ι → ℂ | w i ≠ 0} :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  have hW : IsOpen W := (CoordinateCone.Constructions.Cone.differentiableOn_coordinateRatios i).continuousOn.isOpen_inter_preimage hpatch hO
  let V' := V ×ˢ ({0}ᶜ : Set ℂ)
  let ψ : E × ℂ → (ι → ℂ) := fun p => p.2 • normalizedLift i (φ p.1)
  have hψi (p : E × ℂ) : ψ p i = p.2 := by
    simp only [ψ, Pi.smul_apply, smul_eq_mul, normalizedLift_self, mul_one]
  have hψrat (p : E × ℂ) (hp : p ∈ V') : CoordinateCone.Constructions.Cone.coordinateRatios i (ψ p) = φ p.1 :=
    ratios_smul_normalizedLift i (φ p.1) hp.2
  have hφfst : DifferentiableOn ℂ (fun p : E × ℂ => φ p.1) V' :=
    hφ.comp differentiable_fst.differentiableOn (fun p (hp : p ∈ V') => hp.1)
  have hlift : DifferentiableOn ℂ (fun p : E × ℂ => normalizedLift i (φ p.1)) V' :=
    (differentiable_normalizedLift i).comp_differentiableOn hφfst
  have hψ : DifferentiableOn ℂ ψ V' := differentiable_snd.differentiableOn.fun_smul hlift
  refine ⟨W, V', ψ, hW, ⟨hvi, hvO⟩, hV.prod isClosed_singleton.isOpen_compl, hψ, ?_, ?_, ?_⟩
  · intro w hw
    have hwt : (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm (CoordinateCone.Constructions.Cone.coordinateRatios i w) ∈ Z :=
      (CoordinateCone.Constructions.Cone.mem_projectiveCone_iff_coordinateRatios Z i w hw.2.1).mp hw.1
    obtain ⟨a, ha, hφa⟩ := hsub ⟨hwt, hw.2.2⟩
    refine ⟨(a, w i), ⟨ha, hw.2.1⟩, ?_⟩
    change w i • normalizedLift i (φ a) = w
    rw [hφa]
    exact smul_normalizedLift_ratios i w hw.2.1
  · intro p hp
    apply (CoordinateCone.Constructions.Cone.mem_projectiveCone_iff_coordinateRatios Z i (ψ p) (by rw [hψi]; exact hp.2)).mpr
    rw [hψrat p hp]
    exact hmaps hp.1
  · intro p hp q hq heq
    have ht : p.2 = q.2 := by simpa only [hψi] using congrFun heq i
    have hbase : φ p.1 = φ q.1 := by
      rw [← hψrat p hp, ← hψrat q hq, heq]
    exact Prod.ext (hinj hp.1 hq.1 hbase) ht

omit [Fintype ι] in
theorem exists_nonzero_mem_projectiveCone
    {Z : Set (Projectivization ℂ (ι → ℂ))} (hZ : Z.Nonempty) :
    ∃ v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z, v ≠ 0 := by
  obtain ⟨p, hp⟩ := hZ
  induction p using Projectivization.ind with
  | h v hv => exact ⟨v, fun _ => hp, hv⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone
