import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe
import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Tensor Chain Quotient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions

noncomputable section

section

/-!
# DegreeTwo: descend tensor maps through genuine quotients

Tensoring the two actual cokernel diagrams gives the universal property
needed to descend the cross product. All quotient maps remain the given
maps, including their normalization on representatives.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

def moduleTensorQuotientDesc
    (s t : ShortComplex (ModuleCat.{0} k)) (hs : s.Exact) (ht : t.Exact)
    [Epi s.g] [Epi t.g] {M : ModuleCat.{0} k} (f : s.X₂ ⊗ t.X₂ ⟶ M)
    (hl : (s.f ▷ t.X₂) ≫ f = 0) (hr : (s.X₂ ◁ t.f) ≫ f = 0) :
    s.X₃ ⊗ t.X₃ ⟶ M :=
  (CokernelCofork.IsColimit.desc'
    (CokernelCofork.isColimitTensor hs.gIsCokernel ht.gIsCokernel) f (by
      apply coprod.hom_ext
      · simpa only [coprod.inl_desc_assoc, comp_zero] using hl
      · simpa only [coprod.inr_desc_assoc, comp_zero] using hr)).val

theorem moduleTensorQuotientDesc_fac
    (s t : ShortComplex (ModuleCat.{0} k)) (hs : s.Exact) (ht : t.Exact)
    [Epi s.g] [Epi t.g] {M : ModuleCat.{0} k} (f : s.X₂ ⊗ t.X₂ ⟶ M)
    (hl : (s.f ▷ t.X₂) ≫ f = 0) (hr : (s.X₂ ◁ t.f) ≫ f = 0) :
    (s.g ⊗ₘ t.g) ≫ moduleTensorQuotientDesc s t hs ht f hl hr = f :=
  (CokernelCofork.IsColimit.desc'
    (CokernelCofork.isColimitTensor hs.gIsCokernel ht.gIsCokernel) f _).property

/-- The tensor map of two degreewise quotient maps is degreewise
surjective. This also lets the chain identity be checked before quotienting. -/
theorem tensorChainHom_degree_epi
    {C D C' D' : ChainComplex (ModuleCat.{0} k) ℕ} (f : C ⟶ C') (g : D ⟶ D')
    [∀ n, Epi (f.f n)] [∀ n, Epi (g.f n)] (n : ℕ) : Epi ((f ⊗ₘ g).f n) := by
  constructor
  intro M u v huv
  apply mapBifunctor.hom_ext
  intro p q hpq
  have he : Epi (f.f p ⊗ₘ g.f q) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact TensorProduct.map_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  apply (cancel_epi (f.f p ⊗ₘ g.f q)).mp
  have hh := congrArg
    (fun a => ιTensorObj C D p q n hpq ≫ a) huv
  have hi : ιTensorObj C D p q n hpq ≫ (f ⊗ₘ g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj C' D' p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D f g n ⟨(p, q), hpq⟩
  rw [← Category.assoc, ← Category.assoc, hi, Category.assoc, Category.assoc] at hh
  exact hh

end

/-!
# DegreeTwo: tensor quotient descent as an actual chain map

The map on quotient tensors is constructed in each bidegree. Its chain
identity follows by precomposing with the genuine surjective quotient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]

private theorem tensorBidegree_left_zero
    {C₀ C D E : ChainComplex (ModuleCat.{0} k) ℕ}
    (i : C₀ ⟶ C) (f : C ⊗ D ⟶ E) (hf : (i ⊗ₘ 𝟙 D) ≫ f = 0)
    (p q n : ℕ) (hpq : p + q = n) :
    (i.f p ▷ D.X q) ≫ ιTensorObj C D p q n hpq ≫ f.f n = 0 := by
  have h := congrArg (fun a => ιTensorObj C₀ D p q n hpq ≫ a.f n) hf
  change ιTensorObj C₀ D p q n hpq ≫ (i ⊗ₘ 𝟙 D).f n ≫ f.f n = 0 at h
  have hi : ιTensorObj C₀ D p q n hpq ≫ (i ⊗ₘ 𝟙 D).f n =
      (i.f p ⊗ₘ 𝟙 (D.X q)) ≫ ιTensorObj C D p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C₀ D i (𝟙 D) n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc, tensorHom_id] at h
  exact h

private theorem tensorBidegree_right_zero
    {C D₀ D E : ChainComplex (ModuleCat.{0} k) ℕ}
    (i : D₀ ⟶ D) (f : C ⊗ D ⟶ E) (hf : (𝟙 C ⊗ₘ i) ≫ f = 0)
    (p q n : ℕ) (hpq : p + q = n) :
    (C.X p ◁ i.f q) ≫ ιTensorObj C D p q n hpq ≫ f.f n = 0 := by
  have h := congrArg (fun a => ιTensorObj C D₀ p q n hpq ≫ a.f n) hf
  change ιTensorObj C D₀ p q n hpq ≫ (𝟙 C ⊗ₘ i).f n ≫ f.f n = 0 at h
  have hi : ιTensorObj C D₀ p q n hpq ≫ (𝟙 C ⊗ₘ i).f n =
      (𝟙 (C.X p) ⊗ₘ i.f q) ≫ ιTensorObj C D p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D₀ (𝟙 C) i n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc, id_tensorHom] at h
  exact h

variable (s t : ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ))
variable (hs : s.ShortExact) (ht : t.ShortExact)
variable {E : ChainComplex (ModuleCat.{0} k) ℕ} (f : s.X₂ ⊗ t.X₂ ⟶ E)
variable (hl : (s.f ⊗ₘ 𝟙 t.X₂) ≫ f = 0) (hr : (𝟙 s.X₂ ⊗ₘ t.f) ≫ f = 0)

private def tensorQuotientBidegree (p q n : ℕ) (hpq : p + q = n) :
    s.X₃.X p ⊗ t.X₃.X q ⟶ E.X n := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  letI : Epi sp.g := hsp.epi_g
  letI : Epi tq.g := htq.epi_g
  exact moduleTensorQuotientDesc sp tq hsp.exact htq.exact
    (ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f.f n)
    (tensorBidegree_left_zero s.f f hl p q n hpq)
    (tensorBidegree_right_zero t.f f hr p q n hpq)

private theorem tensorQuotientBidegree_fac (p q n : ℕ) (hpq : p + q = n) :
    (s.g.f p ⊗ₘ t.g.f q) ≫ tensorQuotientBidegree s t hs ht f hl hr p q n hpq =
      ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f.f n := by
  let sp := s.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) p)
  let tq := t.map (HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.down ℕ) q)
  have hsp : sp.ShortExact := (shortExact_iff_degreewise_shortExact s).mp hs p
  have htq : tq.ShortExact := (shortExact_iff_degreewise_shortExact t).mp ht q
  have : Epi sp.g := hsp.epi_g
  have : Epi tq.g := htq.epi_g
  exact moduleTensorQuotientDesc_fac sp tq hsp.exact htq.exact
    (ιTensorObj s.X₂ t.X₂ p q n hpq ≫ f.f n)
    (tensorBidegree_left_zero s.f f hl p q n hpq)
    (tensorBidegree_right_zero t.f f hr p q n hpq)

private def tensorQuotientDegree (n : ℕ) : (s.X₃ ⊗ t.X₃).X n ⟶ E.X n :=
  mapBifunctorDesc (fun p q hpq => tensorQuotientBidegree s t hs ht f hl hr p q n hpq)

private theorem tensorQuotientDegree_fac (n : ℕ) :
    (s.g ⊗ₘ t.g).f n ≫ tensorQuotientDegree s t hs ht f hl hr n = f.f n := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  have hi : ιTensorObj s.X₂ t.X₂ p q n hpq ≫ (s.g ⊗ₘ t.g).f n =
      (s.g.f p ⊗ₘ t.g.f q) ≫ ιTensorObj s.X₃ t.X₃ p q n hpq :=
    AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom s.X₂ t.X₂ s.g t.g n ⟨(p,q), hpq⟩
  rw [← Category.assoc, hi, Category.assoc]
  change _ ≫ (ιTensorObj s.X₃ t.X₃ p q n hpq ≫ mapBifunctorDesc _) = _
  rw [ι_mapBifunctorDesc]
  exact tensorQuotientBidegree_fac s t hs ht f hl hr p q n hpq

/-- Descent of a chain map annihilating both factor subcomplexes. -/
def tensorChainQuotientDesc : s.X₃ ⊗ t.X₃ ⟶ E where
  f n := tensorQuotientDegree s t hs ht f hl hr n
  comm' n m _ := by
    have : ∀ n, Epi (s.g.f n) := fun n =>
      ((shortExact_iff_degreewise_shortExact s).mp hs n).epi_g
    have : ∀ n, Epi (t.g.f n) := fun n =>
      ((shortExact_iff_degreewise_shortExact t).mp ht n).epi_g
    have := tensorChainHom_degree_epi s.g t.g n
    apply (cancel_epi ((s.g ⊗ₘ t.g).f n)).mp
    rw [← Category.assoc, tensorQuotientDegree_fac,
      ← Category.assoc, (s.g ⊗ₘ t.g).comm n m, Category.assoc, tensorQuotientDegree_fac]
    exact f.comm n m

theorem tensorChainQuotientDesc_fac :
    (s.g ⊗ₘ t.g) ≫ tensorChainQuotientDesc s t hs ht f hl hr = f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact tensorQuotientDegree_fac s t hs ht f hl hr n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions
