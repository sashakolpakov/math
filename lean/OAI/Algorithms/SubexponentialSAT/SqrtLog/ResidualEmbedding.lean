import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSquarefree

namespace OAI.Algorithms

/-! Injective padding of residual squarefree variables into their original
ambient coordinate universe. This is a semantic map, not runtime renumbering. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

def supportMap (e : V ↪ W) : Support V →* Support W where
  toFun s := ⟨s.vars.map e⟩
  map_one' := by apply Support.ext; simp
  map_mul' a b := by apply Support.ext; exact Finset.map_union _ _

theorem supportMap_injective (e : V ↪ W) : Function.Injective (supportMap e) := by
  intro a b h
  apply Support.ext
  exact Finset.map_injective e (congrArg Support.vars h)

def poly (e : V ↪ W) : Poly V R →+* Poly W R :=
  MonoidAlgebra.mapDomainRingHom R (supportMap e)

@[simp] theorem poly_monomial (e : V ↪ W) (s : Finset V) (c : R) :
    poly e (monomial s c) = monomial (s.map e) c :=
  MonoidAlgebra.mapDomain_single

@[simp] theorem coeff_poly (e : V ↪ W) (s : Finset V) (f : Poly V R) :
    coeff (s.map e) (poly e f) = coeff s f :=
  Finsupp.mapDomain_apply_of_injective (supportMap_injective e) f.coeff
    (⟨s⟩ : Support V)

theorem coeff_poly_zero (e : V ↪ W) (s : Finset W)
    (hs : ¬ ∃ a : Finset V, a.map e = s) (f : Poly V R) :
    coeff s (poly e f) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨a, ha⟩
  exact hs ⟨a.vars, congrArg Support.vars ha⟩

theorem poly_injective (e : V ↪ W) : Function.Injective (poly e : Poly V R → Poly W R) :=
  MonoidAlgebra.mapDomain_injective (supportMap_injective e)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem weight_map (e : V ↪ W) (x : W → R) (s : Finset V) :
    weight x (s.map e) = weight (fun v => x (e v)) s := by
  simp [weight]

theorem eval_poly (e : V ↪ W) (x : W → R) (hx : ∀ w, x w * x w = x w)
    (f : Poly V R) :
    evalHom x hx (poly e f) =
      evalHom (fun v => x (e v)) (fun v => hx (e v)) f := by
  rw [eval_eq_sum, eval_eq_sum]
  change (Finsupp.mapDomain (supportMap e) f.coeff).sum
      (fun s c => c * weight x s.vars) =
    f.coeff.sum (fun s c => c * weight (fun v => x (e v)) s.vars)
  rw [Finsupp.sum_mapDomain_index_inj (supportMap_injective e)]
  apply Finsupp.sum_congr
  intro a _
  change f.coeff a * weight x (a.vars.map e) =
    f.coeff a * weight (fun v => x (e v)) a.vars
  rw [weight_map]

theorem bounded_poly (e : V ↪ W) {k : ℕ} {f : Poly V R} (hf : Bounded k f) :
    Bounded k (poly e f) := by
  intro s hs
  change s ∈ (Finsupp.mapDomain (supportMap e) f.coeff).support at hs
  have hm := Finsupp.mapDomain_support hs
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
  simpa [supportMap] using hf a ha

def jet (e : V ↪ W) : Jet V R →+* Jet W R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (poly e))

@[simp] theorem jet_coeff (e : V ↪ W) (f : Jet V R) (u z : ℕ) :
    ((jet e f).coeff u).coeff z = poly e ((f.coeff u).coeff z) := by
  simp [jet]

@[simp] theorem jet_canonical (e : V ↪ W) (t J : ℕ) (f : Jet V R) :
    jet e (canonical t J f) = canonical t J (jet e f) := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  by_cases h : u < t ∧ z < J <;> simp [h]

theorem admissible_jet (e : V ↪ W) {f : Jet V R} (hf : Admissible f) :
    Admissible (jet e f) := by
  intro u z
  rw [jet_coeff]
  exact bounded_poly e (hf u z)

@[simp] theorem jetCoeff_jet (e : V ↪ W) (s : Finset V) (f : Jet V R) :
    Moments.jetCoeff ⟨s.map e⟩ (jet e f) = Moments.jetCoeff ⟨s⟩ f := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  simp

theorem jetCoeff_jet_zero (e : V ↪ W) (s : Finset W)
    (hs : ¬ ∃ a : Finset V, a.map e = s) (f : Jet V R) :
    Moments.jetCoeff ⟨s⟩ (jet e f) = 0 := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  simpa using coeff_poly_zero e s hs ((f.coeff u).coeff z)

theorem eval_jet (e : V ↪ W) (x : W → R) (hx : ∀ w, x w * x w = x w)
    (f : Jet V R) :
    Moments.jetEval x hx (jet e f) =
      Moments.jetEval (fun v => x (e v)) (fun v => hx (e v)) f := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  simp only [Moments.jetEval_coeff, jet_coeff]
  exact eval_poly e x hx _

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
