import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Polynomial Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Passing to a positive tensor power scales the variable in the actual section Hilbert polynomial. The proof compares genuine tensor-power section spaces. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Line.Bundles.LineBundle.HasSectionHilbertPolynomial.tensorPower
    {K : Type u} [Field K] {X : Scheme.{u}} {p : X ⟶ Spec (.of K)}
    {L : Line.Bundles.LineBundle X} {P : Polynomial ℚ} (hP : L.HasSectionHilbertPolynomial p P)
    (n : ℕ) (hn : 0 < n) :
    (L.tensorPower n).HasSectionHilbertPolynomial p (P.comp (Polynomial.C (n : ℚ) * Polynomial.X)) := by
  obtain ⟨b, hb⟩ := hP
  refine ⟨b, fun d hd => ?_⟩
  have hdn : b ≤ d * n := hd.trans (Nat.le_mul_of_pos_right d hn)
  obtain ⟨hfinite, heval⟩ := hb (d * n) hdn
  have := hfinite
  let e := ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).mapIso (L.tensorPowerComposeIso d n)).toLinearEquiv
  refine ⟨Module.Finite.equiv e, ?_⟩
  calc
    (P.comp (Polynomial.C (n : ℚ) * Polynomial.X)).eval (d : ℚ) = P.eval ((d * n : ℕ) : ℚ) := by
      simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Nat.cast_mul, mul_comm (n : ℚ) (d : ℚ)]
    _ = (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower (d * n)).sheaf) : ℚ) := heval
    _ = (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj ((L.tensorPower n).tensorPower d).sheaf) : ℚ) :=
      congrArg (fun k : ℕ => (k : ℚ)) e.finrank_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
