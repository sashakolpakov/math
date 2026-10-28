import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ResidueTotal

/-! # Quotient Coefficient Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.QuotientCoefficientPresheaf

noncomputable section

/-! The actual quotient by the normal equations, on every coefficient
open, receives the canonical oriented Koszul residue chain map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c : ℕ} (s : Fin c → R)

def ideal (a : Cᵒᵖ) : Ideal (P.obj a) := Ideal.span (Set.range (algebraMap R (P.obj a) ∘ s))

omit [HasFiniteProducts C] in
theorem ideal_map {a b : Cᵒᵖ} (f : a ⟶ b) :
    ideal R P s a ≤ (ideal R P s b).comap (P.map f).hom := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  change (P.map f).hom (algebraMap R (P.obj a) (s i)) ∈ ideal R P s b
  rw [(P.map f).hom.commutes]
  exact Ideal.subset_span ⟨i, rfl⟩

def quotient : Cᵒᵖ ⥤ CommAlgCat.{u} R where
  obj a := CommAlgCat.of R (P.obj a ⧸ ideal R P s a)
  map {a b} f := CommAlgCat.ofHom (Ideal.quotientMapₐ (ideal R P s b)
    (P.map f).hom (ideal_map R P s f))
  map_id a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((P.map (𝟙 a)).hom x) = Ideal.Quotient.mk _ x
    rw [P.map_id]
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((P.map (f ≫ g)).hom x) =
      Ideal.Quotient.mk _ ((P.map g).hom ((P.map f).hom x))
    rw [P.map_comp]
    rfl

def mk : P ⟶ quotient R P s where
  app a := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (ideal R P s a))
  naturality a b f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

def moduleMk : KoszulPartial.Fractions.modules R P ⟶ KoszulPartial.Fractions.modules R (quotient R P s) :=
  Functor.whiskerRight (QuotientCoefficientPresheaf.mk R P s)
    (forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R))

omit [HasFiniteProducts C] in
theorem annihilated (a : Cᵒᵖ) (i : Fin c) (x : (KoszulPartial.Fractions.modules R (quotient R P s)).obj a) :
    s i • x = 0 := by
  change P.obj a ⧸ ideal R P s a at x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change s i • ((moduleMk R P s).app a y) = 0
  rw [← (moduleMk R P s).app a |>.hom.map_smul]
  change Ideal.Quotient.mk (ideal R P s a) (s i • y) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

def residue : KoszulPartial.Components.coefficient R P s ⟶
    (single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj (KoszulPartial.Fractions.modules R (quotient R P s)) :=
  CoefficientResidue.complexMap R P s (KoszulPartial.Fractions.modules R (quotient R P s))
    (moduleMk R P s) (annihilated R P s)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.QuotientCoefficientPresheaf
