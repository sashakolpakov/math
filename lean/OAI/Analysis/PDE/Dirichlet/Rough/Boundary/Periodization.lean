import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ShiftGeometry
import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentPeriodization

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.SmoothExtension

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

def periodicPerturbation (L : T →+ E) (h : E → E) (x : E) : E :=
  x + OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization L h x

omit [NormedSpace ℝ E] in
theorem periodicPerturbation_add (L : T →+ E) (h : E → E) (z : T) (x : E) :
    periodicPerturbation L h (x + L z) = periodicPerturbation L h x + L z := by
  simp only [periodicPerturbation, OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization_add]
  abel

omit [NormedSpace ℝ E] in
theorem periodicPerturbation_at (L : T →+ E) (h : E → E) {K : Set E}
    (hs : ∀ x ∉ K, h x = 0)
    (hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w)
    (x : E) (z : T) (hz : x + L z ∈ K) :
    periodicPerturbation L h x = x + h (x + L z) := by
  classical
  unfold periodicPerturbation OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization
  congr 1
  apply tsum_eq_single z
  intro w hw
  apply hs
  intro hh
  exact hw (hdis x w z hh hz)

omit [NormedSpace ℝ E] in
theorem periodicPerturbation_eq_self (L : T →+ E) (h : E → E) {K : Set E}
    (hs : ∀ x ∉ K, h x = 0) (x : E) (hx : ∀ z, x + L z ∉ K) :
    periodicPerturbation L h x = x := by
  have he : (fun z ↦ h (x + L z)) = 0 := funext (fun z ↦ hs _ (hx z))
  rw [periodicPerturbation, OAI.Analysis.Calculus.SmoothExtension.vectorPeriodization, he]
  change x + (∑' _ : T, (0 : E)) = x
  rw [tsum_zero, add_zero]

omit [NormedSpace ℝ E] in
/-- Disjoint translated patches preserve actual inverse identities. -/
theorem periodicPerturbation_leftInverse (L : T →+ E) (h g : E → E) {K : Set E}
    (hs : ∀ x ∉ K, h x = 0) (gs : ∀ x ∉ K, g x = 0)
    (hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w)
    (hinv : Function.LeftInverse (fun x ↦ x + g x) (fun x ↦ x + h x)) :
    Function.LeftInverse (periodicPerturbation L g) (periodicPerturbation L h) := by
  classical
  intro x
  by_cases hx : ∃ z, x + L z ∈ K
  · obtain ⟨z, hz⟩ := hx
    have hm : MapsTo (fun x ↦ x + h x) K K :=
      mapsTo_of_injective_eq_self_off hinv.injective (fun x hx ↦ by simp [hs x hx])
    have he : periodicPerturbation L h x + L z = (x + L z) + h (x + L z) := by
      rw [periodicPerturbation_at L h hs hdis x z hz]
      abel
    rw [periodicPerturbation_at L g gs hdis _ z (he.symm ▸ hm hz), he,
      periodicPerturbation_at L h hs hdis x z hz]
    have hh := hinv (x + L z)
    dsimp at hh
    have : h (x + L z) + g (x + L z + h (x + L z)) = 0 := by
      apply add_left_cancel (a := x + L z)
      simpa only [add_assoc, add_zero] using hh
    simpa only [add_assoc, add_zero] using congrArg (fun y ↦ x + y) this
  · have ho : ∀ z, x + L z ∉ K := by simpa only [not_exists] using hx
    rw [periodicPerturbation_eq_self L h hs x ho, periodicPerturbation_eq_self L g gs x ho]

omit [NormedSpace ℝ E] in
theorem periodicPerturbation_bijective (L : T →+ E) (h g : E → E) {K : Set E}
    (hs : ∀ x ∉ K, h x = 0) (gs : ∀ x ∉ K, g x = 0)
    (hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w)
    (hl : Function.LeftInverse (fun x ↦ x + g x) (fun x ↦ x + h x))
    (hr : Function.LeftInverse (fun x ↦ x + h x) (fun x ↦ x + g x)) :
    Function.Bijective (periodicPerturbation L h) :=
  ⟨(periodicPerturbation_leftInverse L h g hs gs hdis hl).injective,
    (periodicPerturbation_leftInverse L g h gs hs hdis hr).surjective⟩

omit [NormedSpace ℝ E] in
theorem periodicPerturbation_preserves_level (L : T →+ E) (h : E → E) (r : E → ℝ)
    {K : Set E} (hs : ∀ x ∉ K, h x = 0)
    (hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w)
    (hr : ∀ x z, r (x + L z) = r x)
    (hl : ∀ x, r (x + h x) = r x) (x : E) :
    r (periodicPerturbation L h x) = r x := by
  classical
  by_cases hx : ∃ z, x + L z ∈ K
  · obtain ⟨z, hz⟩ := hx
    rw [periodicPerturbation_at L h hs hdis x z hz]
    calc
      r (x + h (x + L z)) = r (x + h (x + L z) + L z) := (hr _ z).symm
      _ = r ((x + L z) + h (x + L z)) := by congr 1; abel
      _ = r (x + L z) := hl _
      _ = r x := hr x z
  · rw [periodicPerturbation_eq_self L h hs x (by simpa only [not_exists] using hx)]

end OAI.Analysis.PDE.Dirichlet
