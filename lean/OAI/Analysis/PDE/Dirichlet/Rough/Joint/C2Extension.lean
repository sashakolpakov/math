import OAI.Analysis.PDE.Dirichlet.Rough.Joint.GeometricFamilies
import OAI.Analysis.Normed.Function.Holder.C2HolderJointExtension

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {r : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}

/-- A common-open implicit family with the actual geometric value identity
supplies a genuine joint C² representative near its base parameter, on the
entire closed reference domain. -/
theorem exists_joint_C2_extension_of_family
    (hr : ContDiff ℝ ∞ r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {Φ : T × E → E} (hΦ : ∀ x, Φ (0,x) = x)
    {f : Z × E → ℝ} {U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α}
    {W : Set (Z × T)} (hW : IsOpen W) (hU : ContDiffOn ℝ ∞ U W)
    {p₀ : Z} (hp₀ : (p₀,(0:T)) ∈ W)
    (hvalue : ∀ᶠ p in 𝓝 (p₀,(0:T)), ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) x = f (p.1,Φ (p.2,x))) :
    ∃ S : Set Z, IsOpen S ∧ p₀ ∈ S ∧
      ∃ g : Z × E → ℝ, ContDiff ℝ 2 g ∧
        ∀ p ∈ S, ∀ x, r x ≤ 0 → g (p,x) = f (p,x) := by
  have hc : Continuous (fun p : Z => (p,(0:T))) := continuous_id.prodMk continuous_const
  have hv : ∀ᶠ p in 𝓝 p₀, ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U (p,0)) x = f (p,x) := by
    filter_upwards [(hc.tendsto p₀).eventually hvalue] with p hp
    intro x
    simpa only [hΦ] using hp x
  obtain ⟨S₀,hS₀,hS₀open,hpS₀⟩ := mem_nhds_iff.mp hv
  let S : Set Z := S₀ ∩ (fun p : Z => (p,(0:T))) ⁻¹' W
  have hS : IsOpen S := hS₀open.inter (hW.preimage hc)
  have hpS : p₀ ∈ S := ⟨hpS₀,hp₀⟩
  have hcurve : ContDiffOn ℝ 2 (fun p : Z => U (p,0)) S :=
    (hU.of_le (by simp)).comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun p hp => hp.2)
  obtain ⟨V,hV,hpV,hVS,g,hg,hge⟩ :=
    OAI.Analysis.Normed.Function.Holder.C2Holder.exists_joint_C2_extension_near_parameter hS hr hreg
      (fun p : Z => U (p,0)) hcurve p₀ hpS
  refine ⟨V,hV,hpV,g,hg,?_⟩
  intro p hp x hx
  rw [hge p hp x hx,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (x := x) _ hx]
  exact hS₀ (hVS hp).1 ⟨x,hx⟩

section Geometric
variable [CompleteSpace T] {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The stationary family is admissible. In particular the geometric-family
property contains a genuine smooth parameter family even before any spatial
flow is selected. -/
def stationaryDomainDeformation (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (r : E → ℝ) : ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r where
  map := Prod.snd
  radius := 1
  radius_pos := zero_lt_one
  smooth := contDiff_snd
  at_zero := fun _ => rfl
  bijective := fun _ _ => Function.bijective_id
  inverse_smooth := by
    have he : (fun p : T × E => ParameterDeformation.inverseFamily Prod.snd p.1 p.2) = Prod.snd := by
      funext p
      exact Function.leftInverse_invFun Function.injective_id p.2
    rw [he]
    exact contDiff_snd.contDiffOn
  equivariant := fun _ _ _ => rfl
  open_domain := fun _ _ _ => Iff.rfl
  closed_domain := fun _ _ _ => Iff.rfl

omit [CompleteSpace T] [Fintype ι] in
theorem HasJointGeometricSolutionFamiliesAt.exists_joint_C2_extension
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {f : Z × E → ℝ} {p₀ : Z}
    (hc : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := T) e b r f hΩK α p₀)
    (hr : ContDiff ℝ ∞ r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    ∃ S : Set Z, IsOpen S ∧ p₀ ∈ S ∧
      ∃ g : Z × E → ℝ, ContDiff ℝ 2 g ∧
        ∀ p ∈ S, ∀ x, r x ≤ 0 → g (p,x) = f (p,x) := by
  let D : ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r := ParameterDeformation.stationaryDomainDeformation e b r
  obtain ⟨U,W,hW,hp,hU,hvalue⟩ := hc D
  exact ParameterDeformation.exists_joint_C2_extension_of_family hr hreg D.at_zero hW hU hp hvalue

end Geometric
end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
