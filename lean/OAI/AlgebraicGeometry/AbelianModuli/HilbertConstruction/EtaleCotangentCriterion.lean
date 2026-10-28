import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-! # Etale Cotangent Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleCotangentCriterion

noncomputable section

/-! A cotangent criterion for formal etaleness over a common smooth base. -/

open _root_.Algebra

universe u v w

variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem formallyEtale_of_cotangent_injective [FormallySmooth R T] [FormallyUnramified S T]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) : FormallyEtale S T where
  subsingleton_kaehlerDifferential := inferInstance
  subsingleton_h1Cotangent := by
    have hz (x : H1Cotangent S T) : x = 0 := by
      have hd : H1Cotangent.δ R S T x = 0 := h
        ((H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero x |>.trans (map_zero _).symm)
      obtain ⟨y, rfl⟩ := (H1Cotangent.exact_map_δ R S T x).mp hd
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleCotangentCriterion
