import OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross
import OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotient

/-! # Triple Degree Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleDegreeQuotient

noncomputable section

/-! Descending homogeneous three-factor tensor maps through actual chain quotients. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions.TensorDegree
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotient.Constructions

namespace Constructions

variable {k : Type} [Field k]
variable (s t u : ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ))
variable (hs : s.ShortExact) (ht : t.ShortExact) (hu : u.ShortExact) (n : ℕ)
variable {M : ModuleCat.{0} k} (f : ((s.X₂ ⊗ t.X₂) ⊗ u.X₂).X n ⟶ M)
variable (h₁ : ((s.f ⊗ₘ 𝟙 t.X₂) ⊗ₘ 𝟙 u.X₂).f n ≫ f = 0)
variable (h₂ : ((𝟙 s.X₂ ⊗ₘ t.f) ⊗ₘ 𝟙 u.X₂).f n ≫ f = 0)
variable (h₃ : (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f).f n ≫ f = 0)

include h₁ in
theorem degree_first_zero (p q r : ℕ) (hpqr : (p + q) + r = n) :
    ((s.f.f p ▷ t.X₂.X q) ▷ u.X₂.X r) ≫
      TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f = 0 := by
  have hz := congrArg (fun g => TripleCross.Constructions.TensorDegree.tripleInclusion s.X₁ t.X₂ u.X₂ p q r n hpqr ≫ g) h₁
  rw [← Category.assoc, TripleCross.Constructions.TensorDegree.tripleInclusion_natural, Category.assoc, comp_zero] at hz
  simpa only [HomologicalComplex.id_f, tensorHom_id] using hz

include h₂ in
theorem degree_second_zero (p q r : ℕ) (hpqr : (p + q) + r = n) :
    ((s.X₂.X p ◁ t.f.f q) ▷ u.X₂.X r) ≫
      TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f = 0 := by
  have hz := congrArg (fun g => TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₁ u.X₂ p q r n hpqr ≫ g) h₂
  rw [← Category.assoc, TripleCross.Constructions.TensorDegree.tripleInclusion_natural, Category.assoc, comp_zero] at hz
  simpa only [HomologicalComplex.id_f, id_tensorHom, tensorHom_id] using hz

include h₃ in
theorem degree_third_zero (p q r : ℕ) (hpqr : (p + q) + r = n) :
    ((s.X₂.X p ⊗ t.X₂.X q) ◁ u.f.f r) ≫
      TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f = 0 := by
  have hz := congrArg (fun g => TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₁ p q r n hpqr ≫ g) h₃
  have hi := TripleCross.Constructions.TensorDegree.tripleInclusion_natural (𝟙 s.X₂) (𝟙 t.X₂) u.f p q r n hpqr
  simp only [HomologicalComplex.id_f, id_tensorHom_id] at hi
  simp only [id_tensorHom] at hi hz
  rw [← Category.assoc, hi, Category.assoc, comp_zero] at hz
  exact hz

private def tridegreeDesc (p q r : ℕ) (hpqr : (p + q) + r = n) :
    (s.X₃.X p ⊗ t.X₃.X q) ⊗ u.X₃.X r ⟶ M := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  let ur := u.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) r)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  have hur : ur.ShortExact := (shortExact_iff_degreewise_shortExact u).mp hu r
  let : Epi sp.g := hsp.epi_g
  let : Epi tq.g := htq.epi_g
  let : Epi ur.g := hur.epi_g
  exact TripleQuotient.Constructions.tripleQuotientDesc sp tq ur hsp.exact htq.exact hur.exact
    (TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f)
    (degree_first_zero s t u n f h₁ p q r hpqr)
    (degree_second_zero s t u n f h₂ p q r hpqr)
    (degree_third_zero s t u n f h₃ p q r hpqr)

private theorem tridegreeDesc_fac (p q r : ℕ) (hpqr : (p + q) + r = n) :
    ((s.g.f p ⊗ₘ t.g.f q) ⊗ₘ u.g.f r) ≫
      tridegreeDesc s t u hs ht hu n f h₁ h₂ h₃ p q r hpqr =
        TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  let ur := u.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) r)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  have hur : ur.ShortExact := (shortExact_iff_degreewise_shortExact u).mp hu r
  let : Epi sp.g := hsp.epi_g
  let : Epi tq.g := htq.epi_g
  let : Epi ur.g := hur.epi_g
  exact TripleQuotient.Constructions.tripleQuotientDesc_fac sp tq ur hsp.exact htq.exact hur.exact
    (TripleCross.Constructions.TensorDegree.tripleInclusion s.X₂ t.X₂ u.X₂ p q r n hpqr ≫ f)
    (degree_first_zero s t u n f h₁ p q r hpqr)
    (degree_second_zero s t u n f h₂ p q r hpqr)
    (degree_third_zero s t u n f h₃ p q r hpqr)

def tripleDegreeQuotientDesc : ((s.X₃ ⊗ t.X₃) ⊗ u.X₃).X n ⟶ M :=
  TripleCross.Constructions.TensorDegree.tripleDegreeDesc s.X₃ t.X₃ u.X₃ n (tridegreeDesc s t u hs ht hu n f h₁ h₂ h₃)

theorem tripleDegreeQuotientDesc_fac :
    ((s.g ⊗ₘ t.g) ⊗ₘ u.g).f n ≫ tripleDegreeQuotientDesc s t u hs ht hu n f h₁ h₂ h₃ = f := by
  apply TripleCross.Constructions.TensorDegree.tripleDegree_hom_ext s.X₂ t.X₂ u.X₂ n
  intro p q r hpqr
  rw [← Category.assoc, TripleCross.Constructions.TensorDegree.tripleInclusion_natural, Category.assoc]
  change _ ≫ (TripleCross.Constructions.TensorDegree.tripleInclusion s.X₃ t.X₃ u.X₃ p q r n hpqr ≫
    TripleCross.Constructions.TensorDegree.tripleDegreeDesc s.X₃ t.X₃ u.X₃ n _) = _
  rw [TripleCross.Constructions.TensorDegree.tripleDegreeDesc_fac]
  exact tridegreeDesc_fac s t u hs ht hu n f h₁ h₂ h₃ p q r hpqr

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleDegreeQuotient
