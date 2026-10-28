import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.OrbitMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELOrbitRecovery

/-! # Orbit Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Equality of the actual reference moduli points is exactly the
literal principal SU orbit relation. The resulting quotient map into
the native moduli points is injective. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}

section

theorem Datum.RankThreePELDatum.referencePELObject_iso_orbit (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N]
    (hN : 3 ≤ N) (z w : P.Domain)
    (e : PEL.Objects.PELIso (P.referencePELObject hP z iota κ he N) (P.referencePELObject hP w iota κ he N)) :
    P.OrbitRelation (Groups.principalSpecialUnitary P.b P.lattice N) z w := by
  let F := Reference.Fiber.referenceAnalyticFiber P hP z
  let G := Reference.Fiber.referenceAnalyticFiber P hP w
  let M := Reference.AlgebraicModel.referenceAlgebraicModel F hP
  let W := Reference.AlgebraicModel.referenceAlgebraicModel G hP
  let D := Reference.DualModel.referenceDualModel F hP
  let D' := Reference.DualModel.referenceDualModel G hP
  let p := (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty M D).some
  let q := (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty W D').some
  let C := (Reference.PicardConstruction.referencePicardConstruction_nonempty p).some
  let C' := (Reference.PicardConstruction.referencePicardConstruction_nonempty q).some
  exact C.principalOrbit_of_pelIso C' iota κ he N e hN

end

variable (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (he : κ.comp iota = P.μ)

theorem Models.FinePELModel.referencePoint_eq_iff_principalOrbit (hN : 3 ≤ N) (z w : P.Domain) :
    M.referencePoint hM κ hP he z = M.referencePoint hM κ hP he w ↔
      P.OrbitRelation (Groups.principalSpecialUnitary P.b P.lattice N) z w := by
  constructor
  · intro h
    obtain ⟨e⟩ := (M.referencePoint_eq_iff hM κ hP he z w).mp h
    exact P.referencePELObject_iso_orbit hP iota κ he N hN z w e
  · rintro ⟨g, hg, hw⟩
    let γ : Groups.principalSpecialUnitary P.b P.lattice N := ⟨g, hg⟩
    have h : w = γ • z := Subtype.ext hw
    rw [h]
    exact (M.referencePoint_principal hM κ hP he γ z).symm

theorem Models.FinePELModel.referenceOrbitMap_injective (hN : 3 ≤ N) : Function.Injective (M.referenceOrbitMap hM κ hP he) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h z =>
    induction y using Quotient.inductionOn with
    | h w =>
      intro h
      apply Quotient.sound
      exact (P.principalOrbitSetoid_iff N z w).mpr ((M.referencePoint_eq_iff_principalOrbit hM κ hP he hN z w).mp h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
