import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicWedges
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAdditiveProduct

/-! # Logarithmic Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicNaturality.Forms

noncomputable section

/-! The original symbol maps preserve logarithmic PD forms and their
products. The statement applies directly to the native frame maps,
including restriction of the coefficient ring. -/
universe u
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B]
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal B) (δJ : DividedPowers J)
  (f : A →+* B)
  (F : ∀ n, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n →+ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S B J δJ n)
  (hF : ∀ n a v, F n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI a v) =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S B J δJ (f a) (f ∘ v))

include hF in
theorem addMap_dlog (u : Aˣ) :
    F 1 (LogarithmicForms.dlog R A I δI u) = LogarithmicForms.dlog S B J δJ (Units.map f u) := by
  rw [LogarithmicForms.dlog_symbol, hF, LogarithmicForms.dlog_symbol]
  rfl

include hF in
theorem addMap_logarithmicWedge (n : ℕ) (v : Fin n → Aˣ) :
    F n (LogarithmicWedges.Forms.logarithmicWedge R A I δI n v) =
      LogarithmicWedges.Forms.logarithmicWedge S B J δJ n (fun i => Units.map f (v i)) := by
  induction n with
  | zero =>
      change F 0 (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI 1 (fun i : Fin 0 => i.elim0)) =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S B J δJ 1 (fun i : Fin 0 => i.elim0)
      rw [hF, map_one]
      congr 1
      ext i
      exact i.elim0
  | succ n ih =>
      rw [LogarithmicWedges.Forms.logarithmicWedge, LogarithmicWedges.Forms.logarithmicWedge,
        DeRhamAdditiveProduct.Wedge.addMap_wedge R S A B I δI J δJ f F hF,
        ih, addMap_dlog R S A B I δI J δJ f F hF]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicNaturality.Forms
