import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorChainQuotient

/-! # Tensor Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorDescent.Constructions

noncomputable section

/-! Degreewise tensor quotient descent, also applicable to homotopy components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]
variable (s t : ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ))
variable (hs : s.ShortExact) (ht : t.ShortExact) (n : ℕ)
variable {M : ModuleCat.{0} k} (f : (s.X₂ ⊗ t.X₂).X n ⟶ M)
variable (hl : (s.f ⊗ₘ 𝟙 t.X₂).f n ≫ f = 0)
variable (hr : (𝟙 s.X₂ ⊗ₘ t.f).f n ≫ f = 0)

include hl in
private theorem degreeBidegree_left (p q : ℕ) (hpq : p + q = n) :
    (s.f.f p ▷ t.X₂.X q) ≫ ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f = 0 := by
  have h := congrArg (fun a => ιTensorObj s.X₁ t.X₂ p q n hpq ≫ a) hl
  have hi : ιTensorObj s.X₁ t.X₂ p q n hpq ≫ (s.f ⊗ₘ 𝟙 t.X₂).f n =
      (s.f.f p ⊗ₘ 𝟙 (t.X₂.X q)) ≫ ιTensorObj s.X₂ t.X₂ p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom s.X₁ t.X₂ s.f (𝟙 t.X₂)
      n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc, tensorHom_id, comp_zero] at h
  exact h

include hr in
private theorem degreeBidegree_right (p q : ℕ) (hpq : p + q = n) :
    (s.X₂.X p ◁ t.f.f q) ≫ ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f = 0 := by
  have h := congrArg (fun a => ιTensorObj s.X₂ t.X₁ p q n hpq ≫ a) hr
  have hi : ιTensorObj s.X₂ t.X₁ p q n hpq ≫ (𝟙 s.X₂ ⊗ₘ t.f).f n =
      (𝟙 (s.X₂.X p) ⊗ₘ t.f.f q) ≫ ιTensorObj s.X₂ t.X₂ p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom s.X₂ t.X₁ (𝟙 s.X₂) t.f
      n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc, id_tensorHom, comp_zero] at h
  exact h

private def degreeBidegreeDesc (p q : ℕ) (hpq : p + q = n) :
    s.X₃.X p ⊗ t.X₃.X q ⟶ M := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  letI : Epi sp.g := hsp.epi_g
  letI : Epi tq.g := htq.epi_g
  exact TensorChainQuotient.Constructions.moduleTensorQuotientDesc sp tq hsp.exact htq.exact
    (ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f)
    (degreeBidegree_left s t n f hl p q hpq) (degreeBidegree_right s t n f hr p q hpq)

private theorem degreeBidegreeDesc_fac (p q : ℕ) (hpq : p + q = n) :
    (s.g.f p ⊗ₘ t.g.f q) ≫ degreeBidegreeDesc s t hs ht n f hl hr p q hpq =
      ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  have : Epi sp.g := hsp.epi_g
  have : Epi tq.g := htq.epi_g
  exact TensorChainQuotient.Constructions.moduleTensorQuotientDesc_fac sp tq hsp.exact htq.exact
    (ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f)
    (degreeBidegree_left s t n f hl p q hpq) (degreeBidegree_right s t n f hr p q hpq)

def tensorDegreeQuotientDesc : (s.X₃ ⊗ t.X₃).X n ⟶ M :=
  mapBifunctorDesc (fun p q hpq => degreeBidegreeDesc s t hs ht n f hl hr p q hpq)

theorem tensorDegreeQuotientDesc_fac :
    (s.g ⊗ₘ t.g).f n ≫ tensorDegreeQuotientDesc s t hs ht n f hl hr = f := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  have hi : ιTensorObj s.X₂ t.X₂ p q n hpq ≫ (s.g ⊗ₘ t.g).f n =
      (s.g.f p ⊗ₘ t.g.f q) ≫ ιTensorObj s.X₃ t.X₃ p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom s.X₂ t.X₂ s.g t.g n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc]
  change _ ≫ (ιTensorObj s.X₃ t.X₃ p q n hpq ≫ mapBifunctorDesc _) = _
  rw [ι_mapBifunctorDesc]
  exact degreeBidegreeDesc_fac s t hs ht n f hl hr p q hpq

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorDescent.Constructions
