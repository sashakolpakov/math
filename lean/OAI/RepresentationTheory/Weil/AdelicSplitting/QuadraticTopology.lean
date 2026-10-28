import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase

/-! # Quadratic Topology -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction

noncomputable section

/-! The natural product topology on a quadratic algebra, including the
split algebra. No field structure on a local quadratic algebra is assumed. -/

variable {R S : Type*} [CommRing R] [CommRing S]
  [TopologicalSpace R] [TopologicalSpace S]

instance quadraticTopologicalSpace (d : R) : TopologicalSpace (UnitaryBase.Construction.Quadratic R d) :=
  TopologicalSpace.induced (QuadraticAlgebra.equivProd d 0) inferInstance

theorem quadratic_continuous_re (d : R) :
    Continuous (QuadraticAlgebra.re : UnitaryBase.Construction.Quadratic R d → R) := by
  have h : Continuous (QuadraticAlgebra.equivProd d 0) := continuous_induced_dom
  exact continuous_fst.comp h

theorem quadratic_continuous_im (d : R) :
    Continuous (QuadraticAlgebra.im : UnitaryBase.Construction.Quadratic R d → R) := by
  have h : Continuous (QuadraticAlgebra.equivProd d 0) := continuous_induced_dom
  exact continuous_snd.comp h

theorem quadratic_continuous_iff {X : Type*} [TopologicalSpace X]
    (d : R) (f : X → UnitaryBase.Construction.Quadratic R d) :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).im) := by
  rw [continuous_induced_rng]
  exact continuous_prodMk

instance quadraticIsTopologicalRing [IsTopologicalRing R] (d : R) :
    IsTopologicalRing (UnitaryBase.Construction.Quadratic R d) where
  continuous_add := by
    rw [quadratic_continuous_iff]
    constructor
    · exact ((quadratic_continuous_re d).comp continuous_fst).add
        ((quadratic_continuous_re d).comp continuous_snd)
    · exact ((quadratic_continuous_im d).comp continuous_fst).add
        ((quadratic_continuous_im d).comp continuous_snd)
  continuous_neg := by
    rw [quadratic_continuous_iff]
    exact ⟨(quadratic_continuous_re d).neg, (quadratic_continuous_im d).neg⟩
  continuous_mul := by
    rw [quadratic_continuous_iff]
    have hr₁ := (quadratic_continuous_re d).comp
      (continuous_fst : Continuous (Prod.fst : UnitaryBase.Construction.Quadratic R d × UnitaryBase.Construction.Quadratic R d → _))
    have hr₂ := (quadratic_continuous_re d).comp
      (continuous_snd : Continuous (Prod.snd : UnitaryBase.Construction.Quadratic R d × UnitaryBase.Construction.Quadratic R d → _))
    have hi₁ := (quadratic_continuous_im d).comp
      (continuous_fst : Continuous (Prod.fst : UnitaryBase.Construction.Quadratic R d × UnitaryBase.Construction.Quadratic R d → _))
    have hi₂ := (quadratic_continuous_im d).comp
      (continuous_snd : Continuous (Prod.snd : UnitaryBase.Construction.Quadratic R d × UnitaryBase.Construction.Quadratic R d → _))
    constructor
    · exact (hr₁.mul hr₂).add (((continuous_const.mul hi₁).mul hi₂))
    · convert (hr₁.mul hi₂).add (hi₁.mul hr₂) using 1
      funext x
      simp [QuadraticAlgebra.im_mul]

instance quadraticContinuousStar [IsTopologicalRing R] (d : R) :
    ContinuousStar (UnitaryBase.Construction.Quadratic R d) where
  continuous_star := by
    rw [quadratic_continuous_iff]
    constructor
    · simpa only [QuadraticAlgebra.re_star, zero_mul, add_zero] using
        quadratic_continuous_re d
    · exact (quadratic_continuous_im d).neg

theorem quadraticBaseChange_continuous (f : R →+* S) (hf : Continuous f) (d : R) :
    Continuous (UnitaryBase.Construction.quadraticBaseChange f d) := by
  rw [quadratic_continuous_iff]
  exact ⟨hf.comp (quadratic_continuous_re d), hf.comp (quadratic_continuous_im d)⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction
