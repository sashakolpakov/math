import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Top Homology Cokernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

noncomputable section

/-! Top homology is the cokernel of the incoming differential. The
identification is normalized on actual cycles and is natural in maps of
complexes. In modules it gives the literal quotient by the image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

def shortIso (S : ShortComplex C) (hg : S.g = 0) : S.homology ≅ cokernel S.f :=
  (ShortComplex.LeftHomologyData.ofHasCokernel S hg).homologyIso

@[reassoc]
theorem short_π_iso (S : ShortComplex C) (hg : S.g = 0) :
    S.homologyπ ≫ (shortIso S hg).hom = S.iCycles ≫ cokernel.π S.f := by
  let h := ShortComplex.LeftHomologyData.ofHasCokernel S hg
  have hi : h.cyclesIso.hom = S.iCycles := by
    have hi' := h.cyclesIso_hom_comp_i
    change h.cyclesIso.hom ≫ 𝟙 S.X₂ = S.iCycles at hi'
    exact (Category.comp_id h.cyclesIso.hom).symm.trans hi'
  change S.homologyπ ≫ h.homologyIso.hom = _
  rw [h.homologyπ_comp_homologyIso_hom, hi]
  rfl

def shortClass (S : ShortComplex C) (hg : S.g = 0) : S.X₂ ⟶ S.homology :=
  (S.cyclesIsoX₂ hg).inv ≫ S.homologyπ

@[reassoc]
theorem shortClass_iso (S : ShortComplex C) (hg : S.g = 0) :
    shortClass S hg ≫ (shortIso S hg).hom = cokernel.π S.f := by
  rw [shortClass, Category.assoc, short_π_iso, ← Category.assoc,
    ShortComplex.cyclesIsoX₂_inv_hom_id, Category.id_comp]

@[reassoc]
theorem short_naturality {S T : ShortComplex C} (a : S ⟶ T)
    (hS : S.g = 0) (hT : T.g = 0) :
    ShortComplex.homologyMap a ≫ (shortIso T hT).hom =
      (shortIso S hS).hom ≫ cokernel.map S.f T.f a.τ₁ a.τ₂ a.comm₁₂.symm := by
  apply (cancel_epi S.homologyπ).mp
  calc
    S.homologyπ ≫ (ShortComplex.homologyMap a ≫ (shortIso T hT).hom) =
        ShortComplex.cyclesMap a ≫ (T.homologyπ ≫ (shortIso T hT).hom) := by
      rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc]
    _ = ShortComplex.cyclesMap a ≫ (T.iCycles ≫ cokernel.π T.f) := by rw [short_π_iso]
    _ = S.iCycles ≫ (a.τ₂ ≫ cokernel.π T.f) := by
      rw [← Category.assoc, ShortComplex.cyclesMap_i, Category.assoc]
    _ = S.iCycles ≫ (cokernel.π S.f ≫ cokernel.map S.f T.f a.τ₁ a.τ₂ a.comm₁₂.symm) := by
      rw [cokernel.π_desc]
    _ = S.homologyπ ≫ ((shortIso S hS).hom ≫
        cokernel.map S.f T.f a.τ₁ a.τ₂ a.comm₁₂.symm) := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ cokernel.map S.f T.f a.τ₁ a.τ₂ a.comm₁₂.symm)
          (short_π_iso S hS).symm

variable {ι : Type w} {c : ComplexShape ι}

def iso (K : HomologicalComplex C c) (n : ι) (h : IsZero (K.X (c.next n))) :
    K.homology n ≅ cokernel (K.d (c.prev n) n) :=
  shortIso (K.sc n) (h.eq_of_tgt _ _)

@[reassoc]
theorem π_iso (K : HomologicalComplex C c) (n : ι) (h : IsZero (K.X (c.next n))) :
    K.homologyπ n ≫ (iso K n h).hom = K.iCycles n ≫ cokernel.π (K.d (c.prev n) n) :=
  short_π_iso (K.sc n) (h.eq_of_tgt _ _)

def cycleClass (K : HomologicalComplex C c) (n : ι) (h : IsZero (K.X (c.next n))) :
    K.X n ⟶ K.homology n :=
  shortClass (K.sc n) (h.eq_of_tgt _ _)

@[reassoc]
theorem cycleClass_iso (K : HomologicalComplex C c) (n : ι) (h : IsZero (K.X (c.next n))) :
    cycleClass K n h ≫ (iso K n h).hom = cokernel.π (K.d (c.prev n) n) :=
  shortClass_iso (K.sc n) (h.eq_of_tgt _ _)

@[reassoc]
theorem naturality {K L : HomologicalComplex C c} (a : K ⟶ L) (n : ι)
    (hK : IsZero (K.X (c.next n))) (hL : IsZero (L.X (c.next n))) :
    HomologicalComplex.homologyMap a n ≫ (iso L n hL).hom =
      (iso K n hK).hom ≫ cokernel.map (K.d (c.prev n) n) (L.d (c.prev n) n)
        (a.f (c.prev n)) (a.f n) (a.comm (c.prev n) n).symm :=
  short_naturality ((HomologicalComplex.shortComplexFunctor C c n).map a)
    (hK.eq_of_tgt _ _) (hL.eq_of_tgt _ _)

variable {R : Type u} [Ring R]

def quotientIso (K : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (h : IsZero (K.X (c.next n))) :
    K.homology n ≅ ModuleCat.of R ((K.X n) ⧸ (K.d (c.prev n) n).hom.range) :=
  iso K n h ≪≫ ModuleCat.cokernelIsoRangeQuotient (K.d (c.prev n) n)

@[reassoc]
theorem cycleClass_quotientIso (K : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (h : IsZero (K.X (c.next n))) :
    cycleClass K n h ≫ (quotientIso K n h).hom =
      ModuleCat.ofHom (K.d (c.prev n) n).hom.range.mkQ := by
  rw [quotientIso, Iso.trans_hom, ← Category.assoc, cycleClass_iso,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel
