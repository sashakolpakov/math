import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBases

/-! # Localized Conormal Basis Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport.Bases

noncomputable section

/-! Transport the actual localized bases to an equal named ideal. -/

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)
  (J : Ideal B) (hJ : I.map (algebraMap A B) = J)

def conormalBasisOfEq {c : ℕ} (b : Module.Basis (Fin c) (A ⧸ I) I.Cotangent) :
    Module.Basis (Fin c) (B ⧸ J) J.Cotangent :=
  hJ ▸ LocalizedConormalBases.conormalBasis (B := B) r I b

theorem conormalBasisOfEq_equations {c : ℕ} (b : Module.Basis (Fin c) (A ⧸ I) I.Cotangent)
    (s : Fin c → I) (hb : ∀ i, b i = I.toCotangent (s i)) (i : Fin c) :
    conormalBasisOfEq r I J hJ b i = J.toCotangent
      ⟨algebraMap A B (s i).val, hJ ▸ Ideal.mem_map_of_mem _ (s i).property⟩ := by
  subst J
  exact LocalizedConormalBases.conormalBasis_equations r I b s hb i

def quotientBasisOfEq {g : ℕ} (b : Module.Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k]) :
    Module.Basis (Fin g) (B ⧸ J) Ω[B ⧸ J⁄k] :=
  hJ ▸ LocalizedConormalBases.quotientBasis (B := B) r I b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport.Bases
