import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.OrzechProperty

/-! # From Differentials -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.FromDifferentials

noncomputable section

/-! The Jacobi-Zariski sequence upgrades unramifiedness to formal
etaleness when the absolute differential map is injective. -/

open scoped TensorProduct

universe u v w

variable (K : Type u) (A : Type v) (B : Type w)
  [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  [Algebra.FormallySmooth K B] [Algebra.FormallyUnramified A B]

theorem of_injective (hi : Function.Injective (KaehlerDifferential.mapBaseChange K A B)) :
    Algebra.FormallyEtale A B := by
  constructor
  · infer_instance
  · apply subsingleton_of_forall_eq 0
    intro x
    have hδ : Algebra.H1Cotangent.δ K A B x = 0 := by
      apply hi
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange K A B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ K A B x).mp hδ
    rw [Subsingleton.elim y 0, map_zero]

omit [Algebra.FormallySmooth K B] in
theorem differentials_surjective : Function.Surjective (KaehlerDifferential.mapBaseChange K A B) := by
  intro x
  exact (KaehlerDifferential.exact_mapBaseChange_map K A B x).mp (Subsingleton.elim _ _)

theorem of_finrank_eq [Nontrivial B]
    [Module.Free B (B ⊗[A] Ω[A⁄K])] [Module.Free B Ω[B⁄K]]
    [Module.Finite B (B ⊗[A] Ω[A⁄K])] [Module.Finite B Ω[B⁄K]]
    (hd : Module.finrank B (B ⊗[A] Ω[A⁄K]) = Module.finrank B Ω[B⁄K]) :
    Algebra.FormallyEtale A B := by
  let e : (B ⊗[A] Ω[A⁄K]) ≃ₗ[B] Ω[B⁄K] := LinearEquiv.ofFinrankEq _ _ hd
  apply of_injective K A B
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
    (KaehlerDifferential.mapBaseChange K A B) e.injective (differentials_surjective K A B)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.FromDifferentials
