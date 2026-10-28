import OAI.AlgebraicGeometry.CycleClass.Thom.TripleDegreeQuotient

/-! # Triple Chain Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient

noncomputable section

/-! The chain-map universal property of three genuine factor quotients. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Thom.TripleDegreeQuotient.Constructions

namespace Constructions

variable {k : Type} [Field k]
variable (s t u : ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ))
variable (hs : s.ShortExact) (ht : t.ShortExact) (hu : u.ShortExact)

include hs ht hu in
theorem tripleQuotient_degree_epi (n : ℕ) : Epi (((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n) := by
  let : ∀ n, Epi (s.g.f n) := fun n =>
    ((shortExact_iff_degreewise_shortExact s).mp hs n).epi_g
  let : ∀ n, Epi (t.g.f n) := fun n =>
    ((shortExact_iff_degreewise_shortExact t).mp ht n).epi_g
  let : ∀ n, Epi (u.g.f n) := fun n =>
    ((shortExact_iff_degreewise_shortExact u).mp hu n).epi_g
  let : ∀ n, Epi ((s.g ⊗ₘ t.g).f n) := fun n => HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.tensorChainHom_degree_epi s.g t.g n
  exact HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.tensorChainHom_degree_epi (s.g ⊗ₘ t.g) u.g n

variable {D : ChainComplex (ModuleCat.{0} k) ℕ} (F : (s.X₂ ⊗ t.X₂) ⊗ u.X₂ ⟶ D)
variable (h₁ : ((s.f ⊗ₘ 𝟙 t.X₂) ⊗ₘ 𝟙 u.X₂) ≫ F = 0)
variable (h₂ : ((𝟙 s.X₂ ⊗ₘ t.f) ⊗ₘ 𝟙 u.X₂) ≫ F = 0)
variable (h₃ : (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f) ≫ F = 0)

private def quotientComponent (n : ℕ) : ((s.X₃ ⊗ t.X₃) ⊗ u.X₃).X n ⟶ D.X n :=
  TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc s t u hs ht hu n (F.f n)
    (HomologicalComplex.congr_hom h₁ n) (HomologicalComplex.congr_hom h₂ n)
    (HomologicalComplex.congr_hom h₃ n)

private theorem quotientComponent_fac (n : ℕ) :
    ((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n ≫ quotientComponent s t u hs ht hu F h₁ h₂ h₃ n = F.f n :=
  TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc_fac s t u hs ht hu n (F.f n)
    (HomologicalComplex.congr_hom h₁ n) (HomologicalComplex.congr_hom h₂ n)
    (HomologicalComplex.congr_hom h₃ n)

def tripleChainQuotientDesc : (s.X₃ ⊗ t.X₃) ⊗ u.X₃ ⟶ D where
  f n := quotientComponent s t u hs ht hu F h₁ h₂ h₃ n
  comm' i j _ := by
    let : Epi (((s.g ⊗ₘ t.g) ⊗ₘ u.g).f i) := tripleQuotient_degree_epi s t u hs ht hu i
    apply (cancel_epi (((s.g ⊗ₘ t.g) ⊗ₘ u.g).f i)).mp
    rw [← Category.assoc, quotientComponent_fac]
    rw [← Category.assoc, ((s.g ⊗ₘ t.g) ⊗ₘ u.g).comm i j, Category.assoc,
      quotientComponent_fac]
    exact F.comm i j

theorem tripleChainQuotientDesc_fac :
    ((s.g ⊗ₘ t.g) ⊗ₘ u.g) ≫ tripleChainQuotientDesc s t u hs ht hu F h₁ h₂ h₃ = F := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact quotientComponent_fac s t u hs ht hu F h₁ h₂ h₃ n

theorem tripleChainQuotientDesc_unique (G : (s.X₃ ⊗ t.X₃) ⊗ u.X₃ ⟶ D)
    (hG : ((s.g ⊗ₘ t.g) ⊗ₘ u.g) ≫ G = F) :
    tripleChainQuotientDesc s t u hs ht hu F h₁ h₂ h₃ = G := by
  apply HomologicalComplex.Hom.ext
  funext n
  let : Epi (((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n) := tripleQuotient_degree_epi s t u hs ht hu n
  apply (cancel_epi (((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n)).mp
  change ((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n ≫ quotientComponent s t u hs ht hu F h₁ h₂ h₃ n = _
  rw [quotientComponent_fac]
  exact (HomologicalComplex.congr_hom hG n).symm

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient
