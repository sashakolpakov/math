import Mathlib.RingTheory.RingHom.Smooth

/-! # Formal Smooth Retract -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FormalSmoothRetract.Constructions

noncomputable section

/-! Formal smoothness descends to actual algebra retracts. This follows
directly from lifting maps through square-zero quotient rings. -/

theorem formallySmooth_of_retract {R A B : Type}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FormallySmooth R B] (i : A →ₐ[R] B) (r : B →ₐ[R] A)
    (h : r.comp i = AlgHom.id R A) : Algebra.FormallySmooth R A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro C _ _ I hI q
  obtain ⟨l, hl⟩ := Algebra.FormallySmooth.comp_surjective R B I hI (q.comp r)
  refine ⟨l.comp i, ?_⟩
  rw [← AlgHom.comp_assoc, hl, AlgHom.comp_assoc, h, AlgHom.comp_id]

theorem ringHom_formallySmooth_of_retract {R A B : Type}
    [CommRing R] [CommRing A] [CommRing B]
    (u : R →+* A) (v : R →+* B) (i : A →+* B) (r : B →+* A)
    (hi : i.comp u = v) (hr : r.comp v = u) (h : r.comp i = RingHom.id A)
    (hv : v.FormallySmooth) : u.FormallySmooth := by
  let : Algebra R A := u.toAlgebra
  let : Algebra R B := v.toAlgebra
  let : Algebra.FormallySmooth R B := hv
  let ia : A →ₐ[R] B := { i with commutes' := fun x => RingHom.congr_fun hi x }
  let ra : B →ₐ[R] A := { r with commutes' := fun x => RingHom.congr_fun hr x }
  exact formallySmooth_of_retract ia ra (AlgHom.ext (fun x => RingHom.congr_fun h x))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FormalSmoothRetract.Constructions
