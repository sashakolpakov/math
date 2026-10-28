import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Varying Dual Open Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualOpenFactorization

noncomputable section

section

/-! A factorization through an open subscheme on the actual special
fiber lifts uniquely for varying dual-number families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (k : Type) [Field k]

theorem dualFamilyReduction_natural
    {X Y : Over (Spec (.of (DualNumber k)))} (f : X ⟶ Y) :
    VaryingDualReduction.dualFamilyReduction k X ≫ f.left =
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f).left ≫ VaryingDualReduction.dualFamilyReduction k Y := by
  change pullback.fst X.hom (Smooth.AffineDualProduct.dualBaseReduction k) ≫ f.left =
    pullback.lift (pullback.fst X.hom (Smooth.AffineDualProduct.dualBaseReduction k) ≫ f.left)
      (pullback.snd X.hom (Smooth.AffineDualProduct.dualBaseReduction k)) _ ≫
        pullback.fst Y.hom (Smooth.AffineDualProduct.dualBaseReduction k)
  exact (pullback.lift_fst _ _ _).symm

variable {U V Y : Over (Spec (.of (DualNumber k)))} (j : V ⟶ Y) (f : U ⟶ Y)
    (a : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj U ⟶
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj V)
    (h : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f =
      a ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map j)

include h

theorem dualOpenFactorization_range : Set.range f.left ⊆ Set.range j.left := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨u₀, rfl⟩ := (VaryingDualReduction.dualFamilyReduction k U).surjective u
  refine ⟨VaryingDualReduction.dualFamilyReduction k V (a.left u₀), ?_⟩
  have hj := congrArg (fun b => b (a.left u₀)) (dualFamilyReduction_natural k j)
  have hf := congrArg (fun b => b u₀) (dualFamilyReduction_natural k f)
  have ha := congrArg (fun b => b.left u₀) h
  calc
    j.left (VaryingDualReduction.dualFamilyReduction k V (a.left u₀)) =
        VaryingDualReduction.dualFamilyReduction k Y (((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map j).left (a.left u₀)) := hj
    _ = VaryingDualReduction.dualFamilyReduction k Y (((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f).left u₀) :=
      congrArg (VaryingDualReduction.dualFamilyReduction k Y) ha.symm
    _ = f.left (VaryingDualReduction.dualFamilyReduction k U u₀) := hf.symm

variable [IsOpenImmersion j.left]

def dualOpenFactorizationLift : U ⟶ V :=
  DualOpen.Lifts.overOpenLift j f (dualOpenFactorization_range k j f a h)

theorem dualOpenFactorizationLift_fac : dualOpenFactorizationLift k j f a h ≫ j = f :=
  DualOpen.Lifts.overOpenLift_fac j f (dualOpenFactorization_range k j f a h)

theorem dualOpenFactorizationLift_reduction :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (dualOpenFactorizationLift k j f a h) = a := by
  have : Mono j := Over.mono_of_mono_left j
  have : Mono ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map j) := inferInstance
  apply (cancel_mono ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map j)).mp
  rw [← Functor.map_comp, dualOpenFactorizationLift_fac, h]

theorem existsUnique_dualOpenFactorization :
    ∃! l : U ⟶ V, l ≫ j = f ∧ (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map l = a := by
  have : Mono j := Over.mono_of_mono_left j
  refine ⟨dualOpenFactorizationLift k j f a h,
    ⟨dualOpenFactorizationLift_fac k j f a h, dualOpenFactorizationLift_reduction k j f a h⟩, ?_⟩
  intro l hl
  apply (cancel_mono j).mp
  exact hl.1.trans (dualOpenFactorizationLift_fac k j f a h).symm

end

/-! Compatible isomorphisms of actual reduced opens uniquely determine
the restriction of an ambient isomorphism of varying dual-number families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k]
    {X Y U V : Over (Spec (.of (DualNumber k)))} (e : X ≅ Y) (i : U ⟶ X) (j : V ⟶ Y)
    (a : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj U ≅
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj V)
    (h : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (i ≫ e.hom) =
      a.hom ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map j)

include h

theorem dualOpenRestriction_inverse_reduction :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (j ≫ e.inv) =
      a.inv ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map i := by
  let F := Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)
  change F.map (j ≫ e.inv) = a.inv ≫ F.map i
  apply (cancel_epi a.hom).mp
  rw [F.map_comp]
  calc
    a.hom ≫ (F.map j ≫ F.map e.inv) = F.map (i ≫ e.hom) ≫ F.map e.inv := by
      rw [h, Category.assoc]
    _ = F.map i := by
      rw [← F.map_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = a.hom ≫ (a.inv ≫ F.map i) := by
      rw [← Category.assoc, a.hom_inv_id, Category.id_comp]

variable [IsOpenImmersion i.left] [IsOpenImmersion j.left]

def dualOpenRestrictionIso : U ≅ V := by
  let l := dualOpenFactorizationLift k j (i ≫ e.hom) a.hom h
  let r := dualOpenFactorizationLift k i (j ≫ e.inv) a.inv
    (dualOpenRestriction_inverse_reduction k e i j a h)
  have hl : l ≫ j = i ≫ e.hom := dualOpenFactorizationLift_fac k j (i ≫ e.hom) a.hom h
  have hr : r ≫ i = j ≫ e.inv := dualOpenFactorizationLift_fac k i (j ≫ e.inv) a.inv
    (dualOpenRestriction_inverse_reduction k e i j a h)
  have : Mono i := Over.mono_of_mono_left i
  have : Mono j := Over.mono_of_mono_left j
  refine ⟨l, r, ?_, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hr, ← Category.assoc, hl, Category.assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, hl, ← Category.assoc, hr, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

theorem dualOpenRestrictionIso_hom_fac :
    (dualOpenRestrictionIso k e i j a h).hom ≫ j = i ≫ e.hom :=
  dualOpenFactorizationLift_fac k j (i ≫ e.hom) a.hom h

theorem dualOpenRestrictionIso_reduction :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (dualOpenRestrictionIso k e i j a h).hom = a.hom :=
  dualOpenFactorizationLift_reduction k j (i ≫ e.hom) a.hom h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualOpenFactorization
