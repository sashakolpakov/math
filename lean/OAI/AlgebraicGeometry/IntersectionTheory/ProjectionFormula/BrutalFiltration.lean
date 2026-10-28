import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject

/-! # Brutal Filtration -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration

noncomputable section

section

/-! An increasing filtration of a cochain complex by its tails. Stage `p`
contains degree `n` exactly when `-n ≤ p`. The stages at negative and positive
infinity are zero and the whole complex. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Classical

variable (R : Type) [CommRing R] (A : CochainComplex (ModuleCat.{0} R) ℤ)

def term (p : EInt) (n : ℤ) : Submodule R (A.X n) :=
  if ((-n : ℤ) : EInt) ≤ p then ⊤ else ⊥

theorem term_mono {p q : EInt} (h : p ≤ q) (n : ℤ) : term R A p n ≤ term R A q n := by
  by_cases hp : ((-n : ℤ) : EInt) ≤ p
  · simp only [term, ite_eq_left hp, ite_eq_left (hp.trans h), le_refl]
  · simp only [term, ite_eq_right hp, bot_le]

theorem differential_mem (p : EInt) (n m : ℤ) (x : A.X n) (hx : x ∈ term R A p n) :
    (A.d n m).hom x ∈ term R A p m := by
  by_cases hm : ((-m : ℤ) : EInt) ≤ p
  · simp only [term, ite_eq_left hm, Submodule.mem_top]
  · by_cases hnm : n + 1 = m
    · have hmn : ((-m : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) := by
        exact WithBotTop.coe_le_coe.mpr (show -m ≤ -n by omega)
      have hn : ¬ ((-n : ℤ) : EInt) ≤ p := fun hn => hm (hmn.trans hn)
      have hx0 : x = 0 := by simpa only [term, ite_eq_right hn, Submodule.mem_bot] using hx
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    · have hz : A.d n m = 0 := A.shape n m hnm
      rw [hz]
      exact Submodule.zero_mem _

def complex (p : EInt) : CochainComplex (ModuleCat.{0} R) ℤ where
  X n := ModuleCat.of R (term R A p n)
  d n m := ModuleCat.ofHom (((A.d n m).hom.comp (term R A p n).subtype).codRestrict
    (term R A p m) (fun x => differential_mem R A p n m x.val x.property))
  shape n m hnm := by
    ext x
    change (A.d n m).hom x.val = 0
    rw [A.shape n m hnm]
    rfl
  d_comp_d' n m k _ _ := by
    ext x
    exact congrArg (fun f : A.X n ⟶ A.X k => f.hom x.val) (A.d_comp_d n m k)

def inclusion {p q : EInt} (h : p ≤ q) : complex R A p ⟶ complex R A q where
  f n := ModuleCat.ofHom (Submodule.inclusion (term_mono R A h n))
  comm' n m _ := by
    ext x
    rfl

def filtration : EInt ⥤ CochainComplex (ModuleCat.{0} R) ℤ where
  obj := complex R A
  map f := BrutalFiltration.inclusion R A (leOfHom f)
  map_id p := by
    apply HomologicalComplex.Hom.ext
    funext n
    ext x
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    ext x
    rfl

def toComplex (p : EInt) : complex R A p ⟶ A where
  f n := ModuleCat.ofHom (term R A p n).subtype
  comm' n m _ := by
    ext x
    rfl

theorem toComplex_mono (p : EInt) : Mono (toComplex R A p) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

theorem zero_below (p : EInt) (n : ℤ) (hn : ¬ ((-n : ℤ) : EInt) ≤ p) :
    IsZero ((complex R A p).X n) := by
  let : Subsingleton (term R A p n) := by
    dsimp only [term]
    rw [ite_eq_right hn]
    infer_instance
  change IsZero (ModuleCat.of R (term R A p n))
  exact ModuleCat.isZero_of_subsingleton _

def termIso (p : EInt) (n : ℤ) (hn : ((-n : ℤ) : EInt) ≤ p) :
    (complex R A p).X n ≅ A.X n :=
  (LinearEquiv.ofBijective (term R A p n).subtype
    ⟨Subtype.val_injective, fun x => ⟨⟨x, by simp only [term, ite_eq_left hn, Submodule.mem_top]⟩, rfl⟩⟩).toModuleIso

theorem termIso_hom (p : EInt) (n : ℤ) (hn : ((-n : ℤ) : EInt) ≤ p) :
    (termIso R A p n hn).hom = (toComplex R A p).f n := rfl

theorem toComplex_f_isIso (p : EInt) (n : ℤ) (hn : ((-n : ℤ) : EInt) ≤ p) :
    IsIso ((toComplex R A p).f n) := by
  rw [← termIso_hom R A p n hn]
  infer_instance

def topIso : complex R A ⊤ ≅ A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => termIso R A ⊤ n le_top)
    (fun n m _ => by
      rw [termIso_hom, termIso_hom]
      exact (toComplex R A ⊤).comm n m)

theorem bot_isZero : IsZero (complex R A ⊥) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext n
  exact (zero_below R A ⊥ n (by simp)).eq_of_src _ _

theorem inclusion_toComplex {p q : EInt} (h : p ≤ q) :
    BrutalFiltration.inclusion R A h ≫ toComplex R A q = toComplex R A p := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

theorem inclusion_f_isIso {p q : EInt} (h : p ≤ q) (n : ℤ)
    (hn : ((-n : ℤ) : EInt) ≤ p) : IsIso ((BrutalFiltration.inclusion R A h).f n) := by
  let := toComplex_f_isIso R A p n hn
  let := toComplex_f_isIso R A q n (hn.trans h)
  have he : (BrutalFiltration.inclusion R A h).f n ≫ (toComplex R A q).f n = (toComplex R A p).f n := rfl
  exact IsIso.of_isIso_fac_right he

end

/-! A complex supported in a finite interval has zero lower filtration
stages and constant upper stages, through the native inclusion maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Bounds

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration

variable (R : Type) [CommRing R] (A : CochainComplex (ModuleCat.{0} R) ℤ)

theorem term_zero (p : EInt) (i : ℤ) (h : IsZero (A.X i)) : IsZero ((complex R A p).X i) := by
  let : Mono ((toComplex R A p).f i) := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  exact IsZero.of_mono ((toComplex R A p).f i) h

theorem stage_zero (u p : ℤ) (hA : ∀ i, u < i → IsZero (A.X i)) (hp : p < -u) :
    IsZero (complex R A (p : EInt)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : -i ≤ p
  · exact (term_zero R A (p : EInt) i (hA i (by omega))).eq_of_src _ _
  · exact (zero_below R A (p : EInt) i (fun h => hi (WithBotTop.coe_le_coe.mp h))).eq_of_src _ _

theorem toComplex_isIso (l p : ℤ) (hA : ∀ i, i < l → IsZero (A.X i)) (hp : -l ≤ p) :
    IsIso (toComplex R A (p : EInt)) := by
  let : ∀ i, IsIso ((toComplex R A (p : EInt)).f i) := by
    intro i
    by_cases hi : -i ≤ p
    · exact toComplex_f_isIso R A (p : EInt) i (WithBotTop.coe_le_coe.mpr hi)
    · have hz := hA i (by omega)
      exact (term_zero R A (p : EInt) i hz).isIso hz _
  exact HomologicalComplex.Hom.isIso_of_components _

theorem inclusion_isIso_above (l p q : ℤ) (hpq : p ≤ q)
    (hA : ∀ i, i < l → IsZero (A.X i)) (hp : -l ≤ p) :
    IsIso (BrutalFiltration.inclusion R A (WithBotTop.coe_le_coe.mpr hpq)) := by
  let := toComplex_isIso R A l p hA hp
  let := toComplex_isIso R A l q hA (hp.trans hpq)
  exact IsIso.of_isIso_fac_right (inclusion_toComplex R A (WithBotTop.coe_le_coe.mpr hpq))

theorem inclusion_isIso_below (u p q : ℤ) (hpq : p ≤ q)
    (hA : ∀ i, u < i → IsZero (A.X i)) (hq : q < -u) :
    IsIso (BrutalFiltration.inclusion R A (WithBotTop.coe_le_coe.mpr hpq)) :=
  (stage_zero R A u p hA (lt_of_le_of_lt hpq hq)).isIso (stage_zero R A u q hA hq) _

end Bounds

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration
