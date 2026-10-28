import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Surjectivity
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Fppf Point Roots -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every test-scheme point admits an N-th root on an actual fppf covering sieve when full level N is present. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
include level

theorem Abelian.Schemes.AbelianScheme.fullLevel_fppf_pointRoots (T : Over S) (a : T ⟶ A.scheme) :
    ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
      ∀ {U : Over S} (f : U ⟶ T), R f → ∃ b : U ⟶ A.scheme, b ^ N = f ≫ a := by
  let Q := Limits.pullback (A.multiplication N) a
  let p : Q ⟶ T := Limits.pullback.snd (A.multiplication N) a
  let b : Q ⟶ A.scheme := Limits.pullback.fst (A.multiplication N) a
  let H := (IsPullback.of_hasPullback (A.multiplication N) a).map (Over.forget S)
  have : Etale p.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) H
      (A.fullLevel_multiplication_etale level)
  have : Surjective p.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) H
      (A.fullLevel_multiplication_surjective level)
  let R₀ := Sieve.generate (Presieve.singleton p.left)
  let R := (Sieve.overEquiv T).symm R₀
  have hR₀ : R₀ ∈ Scheme.fppfTopology T.left :=
    Precoverage.generate_mem_toGrothendieck p.left.singleton_mem_fppfPrecoverage
  refine ⟨R, Scheme.fppfTopology.overEquiv_symm_mem_over T R₀ hR₀, ?_⟩
  intro U f hf
  have hf₀ : R₀ f.left := (Sieve.overEquiv_symm_iff R₀ f).mp hf
  obtain ⟨W, h, k, hk, hfactor⟩ := hf₀
  cases hk
  let hOver : U ⟶ Q := Over.homMk h (by
    calc
      h ≫ Q.hom = h ≫ p.left ≫ T.hom := congrArg (fun z => h ≫ z) p.w.symm
      _ = (h ≫ p.left) ≫ T.hom := (Category.assoc _ _ _).symm
      _ = f.left ≫ T.hom := congrArg (fun z => z ≫ T.hom) hfactor
      _ = U.hom := f.w)
  have hfactorOver : hOver ≫ p = f := by
    apply Over.OverMorphism.ext
    exact hfactor
  have hb : b ^ N = p ≫ a :=
    (A.comp_multiplication N b).symm.trans Limits.pullback.condition
  refine ⟨hOver ≫ b, ?_⟩
  calc
    (hOver ≫ b) ^ N = hOver ≫ b ^ N := by rw [MonObj.comp_pow]
    _ = hOver ≫ p ≫ a := congrArg (fun z => hOver ≫ z) hb
    _ = (hOver ≫ p) ≫ a := (Category.assoc _ _ _).symm
    _ = f ≫ a := congrArg (fun z => z ≫ a) hfactorOver

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
