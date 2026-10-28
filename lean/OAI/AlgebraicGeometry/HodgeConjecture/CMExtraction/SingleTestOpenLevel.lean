import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Single Test Open Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel.Transport

noncomputable section

section

/-! The full AdelicTheta descent conclusion supplies a compact open level
fixing a specified actual finite test, with its principal subgroup. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (frames : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C frames)

def SingleTestLevel (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (K₀ : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
    (∀ g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val, RepresentationTheory.Theta.Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
    ∃ L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
      (∀ g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val, RepresentationTheory.Theta.Adelic.BallGeometryData.PrincipalLevel N g → RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
      ∀ g ∈ L, RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction F H K hd C frames D g f = f

theorem single_test_level_from_descent (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (hDescent : RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B frames hd C D) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (K₀ : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ) (hN₀ : 0 < N₀) :
    SingleTestLevel frames hd C D f K₀ N₀ := by
  obtain ⟨N, hN, hdiv, htor, L, hcompact, hle, hprincipal, hfixed, _⟩ :=
    hDescent {f} K₀ N₀ hN₀
  exact ⟨N, hN, hdiv, htor, L, hcompact, hle, hprincipal,
    hfixed f (Finset.mem_singleton_self f)⟩

end

/-! The full AdelicTheta descent conclusion supplies a compact open level
fixing a specified actual finite test, with its principal subgroup. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (frames : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C frames)

theorem exists_single_test_open_level (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (hDescent : RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B frames hd C D) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    ∃ L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H), ∀ g ∈ L, RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction F H K hd C frames D g f = f := by
  obtain ⟨_, _, _, _, L, _, _, _, hfixed⟩ :=
    single_test_level_from_descent frames hd C D B hDescent f ⊤ 1 (by omega)
  exact ⟨L, hfixed⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel.Transport
